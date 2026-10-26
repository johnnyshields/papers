/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.NonVLegality

/-!
# The two end interfaces of the ordinary non-V family

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:non-v-family`).

Both cells in each marked copy share an edge with the actual middle. Neither copy has
exactly one adjacent cell, so the ordinary Hypothesis V fails at both ends.

Sorry-free.
-/

namespace SkewCornerDescent
open SkewGluing SkewGluing.MarkedInner

/-- Both distinct cells in the lower copy have actual middle neighbors. -/
theorem nonVMark_lower_neighbors (k : ℕ) (hk : 3 ≤ k) :
    ((-1, 0) ∈ (nonVMark k).W ∧
      ∃ y ∈ (nonVMark k).middle, CellAdj (-1, 0) y) ∧
    ((0, 0) ∈ (nonVMark k).W ∧
      ∃ y ∈ (nonVMark k).middle, CellAdj (0, 0) y) := by
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  constructor
  · refine ⟨by simp [nonVMark], (-1, 1), ?_, ?_⟩
    · rw [mem_nonVMark_middle k hk]; omega
    · rw [cellAdj_iff]; norm_num
  · refine ⟨by simp [nonVMark], (0, 1), ?_, ?_⟩
    · rw [mem_nonVMark_middle k hk]; omega
    · rw [cellAdj_iff]; norm_num

/-- Both distinct cells in the upper copy have actual middle neighbors. -/
theorem nonVMark_upper_neighbors (k : ℕ) (hk : 3 ≤ k) :
    ((-2, (k : ℤ) - 1) ∈ (nonVMark k).upper ∧
      ∃ y ∈ (nonVMark k).middle, CellAdj (-2, (k : ℤ) - 1) y) ∧
    ((-1, (k : ℤ) - 1) ∈ (nonVMark k).upper ∧
      ∃ y ∈ (nonVMark k).middle, CellAdj (-1, (k : ℤ) - 1) y) := by
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  constructor
  · refine ⟨by rw [nonVMark_upper]; simp, (-2, (k : ℤ) - 2), ?_, ?_⟩
    · rw [mem_nonVMark_middle k hk]; omega
    · rw [cellAdj_iff]; omega
  · refine ⟨by rw [nonVMark_upper]; simp, (-1, (k : ℤ) - 2), ?_, ?_⟩
    · rw [mem_nonVMark_middle k hk]; omega
    · rw [cellAdj_iff]; omega

/-- Neither marked copy has the unique adjacent cell required by ordinary Hypothesis V. -/
theorem nonVMark_fails_hypothesisV (k : ℕ) (hk : 3 ≤ k) :
    ¬ ((∃! x, x ∈ (nonVMark k).W ∧ ∃ y ∈ (nonVMark k).middle, CellAdj x y) ∨
      (∃! x, x ∈ (nonVMark k).upper ∧ ∃ y ∈ (nonVMark k).middle, CellAdj x y)) := by
  rintro (⟨x, _, hu⟩ | ⟨x, _, hu⟩)
  · have h := nonVMark_lower_neighbors k hk
    have he := (hu _ h.1).trans (hu _ h.2).symm
    norm_num at he
  · have h := nonVMark_upper_neighbors k hk
    have he := (hu _ h.1).trans (hu _ h.2).symm
    norm_num at he

end SkewCornerDescent
