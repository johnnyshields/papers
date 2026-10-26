/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.ThreeRowRigidity

/-!
# Small-row and nonnegative-board rigidity

Both assertions of `lem:small-rows` in
`shields-2026-skew-jacobi-negative.tex`, against arbitrary connected mates.
The full determinant produces the mate's row count before the one-, two-,
and three-row proofs are applied.  Common row and column beta entries are allowed.
-/

namespace SkewJacobiNegative.BetaDiagram
variable {n m : ℕ}

/-- Every connected full board with at most three nonempty rows is rotation-rigid. -/
theorem small_rows_rigidity_same_order (D E : BetaDiagram n)
    (hD : D.Connected) (hE : E.Connected) (hn : n ≤ 3)
    (he : D.schur = E.schur) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  have hpos := hD.1
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact Or.inl (D.rigidity_one E he)
  · exact D.rigidity_two E hD hE he
  · exact D.rigidity_three E hD hE he

/-- `lem:small-rows`: the unknown mate has no order or beta-disjointness restriction. -/
theorem small_rows_rigidity (D : BetaDiagram n) (E : BetaDiagram m)
    (hD : D.Connected) (hE : E.Connected) (hn : n ≤ 3)
    (he : D.schur = E.schur) :
    ∃ hnm : n = m,
      D.TranslationEquivalent (hnm.symm ▸ E) ∨ D.RotationEquivalent (hnm.symm ▸ E) := by
  have hnm := D.row_count_of_schur_eq E he
  subst m
  exact ⟨rfl, D.small_rows_rigidity_same_order E hD hE hn he⟩

/-- The arbitrary-row-count nonnegative assertion of `lem:small-rows`. -/
theorem nonnegative_board_rigidity (D : BetaDiagram n) (E : BetaDiagram m)
    (hD : D.Connected) (hE : E.Connected) (hN : D.Nonnegative)
    (he : D.schur = E.schur) :
    ∃ hnm : n = m,
      D.TranslationEquivalent (hnm.symm ▸ E) ∨ D.RotationEquivalent (hnm.symm ▸ E) :=
  D.nonnegative_rigidity E hD hE hN he

end SkewJacobiNegative.BetaDiagram
