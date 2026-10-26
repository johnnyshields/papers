/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivateUnitProjection

/-!
# The complete two-sided index partition after deleting a private unit

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Strict actual beta geometry partitions every nonunit index into the lower or
upper side. The equivalence preserves both endpoint lists and does not compare
only diagonal inverse entries. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Complete nonunit indices are exactly the two strict sides of a private
cut. The inverse equivalence preserves the full original row and column lists. -/
theorem private_nonunit_sides_equiv {α : Type*} (row col : α → ℤ) (k : ℤ)
    (htri : ∀ a, (row a < k ∧ col a < k) ∨ (k < row a ∧ k < col a) ∨
      (row a = k ∧ col a = k)) :
    ∃ e : {a : α // ¬ (row a = k ∧ col a = k)} ≃
      ({a : α // row a < k} ⊕ {a : α // k < col a}),
      ∀ j, row (e.symm j).val = Sum.elim (fun a => row a.val) (fun a => row a.val) j ∧
        col (e.symm j).val = Sum.elim (fun a => col a.val) (fun a => col a.val) j := by
  classical
  let old := {a : α // ¬ (row a = k ∧ col a = k)}
  let below : old → Prop := fun a => row a.val < k
  let left := Equiv.subtypeSubtypeEquivSubtype
    (p := fun a : α => ¬ (row a = k ∧ col a = k))
    (q := fun a => row a < k) (fun {a} ha => by
      intro h
      rw [h.1] at ha
      exact lt_irrefl _ ha)
  have hright (a : old) : ¬ below a ↔ k < col a.val := by
    rcases htri a.val with h | h | h
    · constructor
      · intro hn
        exact False.elim (hn h.1)
      · intro hn
        exact False.elim (lt_asymm hn h.2)
    · exact ⟨fun _ => h.2, fun _ => not_lt_of_gt h.1⟩
    · exact False.elim (a.property h)
  let right := (Equiv.subtypeEquivRight hright).trans
    (Equiv.subtypeSubtypeEquivSubtype
      (p := fun a : α => ¬ (row a = k ∧ col a = k))
      (q := fun a => k < col a) (fun {a} ha => by
        intro h
        rw [h.2] at ha
        exact lt_irrefl _ ha))
  let e := (Equiv.sumCompl below).symm.trans (Equiv.sumCongr left right)
  refine ⟨e, ?_⟩
  intro j
  rcases j with j | j <;> exact ⟨rfl, rfl⟩

end SkewCornerDescent.Matrix
