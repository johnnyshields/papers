/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Linear inverse windows with all literal starts

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Windows preserve indexed multiplicity; a window longer than the word has no start.
Sorry-free.
-/

namespace SkewCornerDescent

/-- The complete linear inverse-window sum. Empty windows have one start at each
boundary; windows longer than the word have no start. -/
noncomputable def linearInverseWindowSum {L : ℕ} {F : Type*} [Field F]
    (word : Fin L → F) (j : ℕ) : F :=
  ∑ s : Fin (L + 1 - j), ∏ a : Fin j,
    (word ⟨s.val + a.val, by have := s.isLt; have := a.isLt; omega⟩)⁻¹

end SkewCornerDescent
