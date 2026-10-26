/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.LowNegativePatterns

/-!
# Actual masks of small-negative boards

The finite-area southwest argument underlying `lem:small-negative-endpoint`
and its uses in `sec:threshold-proof` of
`shields-2026-skew-jacobi-negative.tex`.  The alternatives are derived from
the actual negative sites, not supplied as source pattern certificates.
-/

namespace SkewJacobiNegative.BetaDiagram
variable {n : ℕ}

/-- A length-three column and a second-column tip exhaust a four-site budget. -/
theorem hook_negatives_of_small_count (D : BetaDiagram (n + 5))
    (hCount : negativeCount D ≤ 4)
    (hColumn : D.row ⟨n + 2, by omega⟩ < D.col 0)
    (hTip : D.row (Fin.last (n + 4)) < D.col 1) : D.HookNegatives := by
  classical
  let a : Fin (n + 5) := ⟨n + 2, by omega⟩
  let b : Fin (n + 5) := ⟨n + 3, by omega⟩
  let c : Fin (n + 5) := Fin.last (n + 4)
  let S : Finset (Fin (n + 5) × Fin (n + 5)) := {(a, 0), (b, 0), (c, 0), (c, 1)}
  have hS : S ⊆ negativeSites D := by
    intro p hp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (D.mem_negativeSites _ _).mpr hColumn
    · exact (D.mem_negativeSites _ _).mpr
        (D.negative_southwest hColumn (by change n + 2 ≤ n + 3; omega) le_rfl)
    · exact (D.mem_negativeSites _ _).mpr
        (D.negative_southwest hColumn (Fin.le_last _) le_rfl)
    · exact (D.mem_negativeSites _ _).mpr hTip
  have hcard : S.card = 4 := by
    norm_num [S, a, b, c, Fin.ext_iff]
  have he : negativeSites D = S := by
    symm
    apply Finset.eq_of_subset_of_card_le hS
    change negativeCount D ≤ S.card
    rwa [hcard]
  intro i j
  rw [← D.mem_negativeSites i j, he]
  simp only [S, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    Fin.ext_iff]
  dsimp [a, b, c]
  have hi := i.isLt
  have hj := j.isLt
  change ((i.val = n + 2 ∧ j.val = 0) ∨ (i.val = n + 3 ∧ j.val = 0) ∨
    (i.val = n + 4 ∧ j.val = 0) ∨ (i.val = n + 4 ∧ j.val = 1)) ↔ _
  omega

/-- One actual two-by-two southwest rectangle exhausts the same budget. -/
theorem square_negatives_of_small_count (D : BetaDiagram (n + 5))
    (hCount : negativeCount D ≤ 4)
    (hSquare : D.row ⟨n + 3, by omega⟩ < D.col 1) : D.SquareNegatives := by
  classical
  let a : Fin (n + 5) := ⟨n + 3, by omega⟩
  let b : Fin (n + 5) := Fin.last (n + 4)
  let S : Finset (Fin (n + 5) × Fin (n + 5)) := {(a, 0), (a, 1), (b, 0), (b, 1)}
  have hS : S ⊆ negativeSites D := by
    intro p hp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (D.mem_negativeSites _ _).mpr
        (D.negative_southwest hSquare le_rfl (by change (0 : ℕ) ≤ 1; omega))
    · exact (D.mem_negativeSites _ _).mpr hSquare
    · exact (D.mem_negativeSites _ _).mpr
        (D.negative_southwest hSquare (Fin.le_last _) (by change (0 : ℕ) ≤ 1; omega))
    · exact (D.mem_negativeSites _ _).mpr
        (D.negative_southwest hSquare (Fin.le_last _) le_rfl)
  have hcard : S.card = 4 := by
    norm_num [S, a, b, Fin.ext_iff]
  have he : negativeSites D = S := by
    symm
    apply Finset.eq_of_subset_of_card_le hS
    change negativeCount D ≤ S.card
    rwa [hcard]
  intro i j
  rw [← D.mem_negativeSites i j, he]
  simp only [S, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    Fin.ext_iff]
  dsimp [a, b]
  have hi := i.isLt
  have hj := j.isLt
  change ((i.val = n + 3 ∧ j.val = 0) ∨ (i.val = n + 3 ∧ j.val = 1) ∨
    (i.val = n + 4 ∧ j.val = 0) ∨ (i.val = n + 4 ∧ j.val = 1)) ↔ _
  omega

/-- Every actual board of order at least five and area at most four has one of
the manuscript's column, three-corner, square or hook shapes.  Weak beta
comparisons and all common-beta boundaries remain in their original form. -/
theorem small_negative_shape_dichotomy (D : BetaDiagram (n + 5))
    (hCount : negativeCount D ≤ 4) :
    D.ColumnNegatives ∨ D.rotate.ColumnNegatives ∨ D.ThreeCorners ∨
      D.SquareNegatives ∨ D.HookNegatives ∨ D.rotate.HookNegatives := by
  by_cases hC : D.ColumnNegatives
  · exact Or.inl hC
  right
  by_cases hCR : D.rotate.ColumnNegatives
  · exact Or.inl hCR
  right
  have hTip : D.row (Fin.last (n + 4)) < D.col 1 := by
    have hn := (D.column_negatives_iff_last_row).not.mp hC
    exact lt_of_not_ge hn
  have hPen : D.row ⟨n + 3, by omega⟩ < D.col 0 := by
    have hn := (D.rotate_column_negatives_iff_penultimate_row).not.mp hCR
    have he : (Fin.last (n + 3)).castSucc = (⟨n + 3, by omega⟩ : Fin (n + 5)) := by
      apply Fin.ext
      rfl
    rw [he] at hn
    exact lt_of_not_ge hn
  by_cases hThree : D.ThreeCorners
  · exact Or.inl hThree
  right
  by_cases hSquare : D.row ⟨n + 3, by omega⟩ < D.col 1
  · exact Or.inl (D.square_negatives_of_small_count hCount hSquare)
  right
  by_cases hHook : D.row ⟨n + 2, by omega⟩ < D.col 0
  · exact Or.inl (D.hook_negatives_of_small_count hCount hHook hTip)
  right
  have hLast : D.row (Fin.last (n + 4)) < D.col 2 := by
    apply lt_of_not_ge
    intro hh
    apply hThree
    exact ⟨le_of_not_gt hHook, le_of_not_gt hSquare, hh⟩
  have hCountR : negativeCount D.rotate ≤ 4 := by
    rw [D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur]
    exact hCount
  apply D.rotate.hook_negatives_of_small_count hCountR
  · rw [D.rotate_negative_iff]
    have h2 : (2 : Fin (n + 5)).val = 2 := by
      change 2 % (n + 5) = 2
      exact Nat.mod_eq_of_lt (by omega)
    have he : (⟨n + 2, by omega⟩ : Fin (n + 5)).rev = 2 := by
      apply Fin.ext
      simp only [Fin.val_rev, h2]
      omega
    simpa only [Fin.rev_zero, he] using hLast
  · rw [D.rotate_negative_iff]
    have h1 : (1 : Fin (n + 5)).val = 1 := by
      change 1 % (n + 5) = 1
      exact Nat.mod_eq_of_lt (by omega)
    have he : (1 : Fin (n + 5)).rev = (⟨n + 3, by omega⟩ : Fin (n + 5)) := by
      apply Fin.ext
      simp only [Fin.val_rev, h1]
      omega
    simpa only [Fin.rev_last, he] using hPen

end SkewJacobiNegative.BetaDiagram
