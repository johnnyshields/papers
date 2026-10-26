/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.SaturatedColumnGeometry
import SkewJacobiNegative.SingletonLift

/-!
# Literal singleton context of a saturated column

The geometric reconstruction in `thm:saturated-column`.  The nonlinear
core, its zero-freeness, and every positive context parameter are produced
from the actual source beta lists.
-/
namespace SkewJacobiNegative.BetaDiagram
variable {n : ℕ}

/-- The budget core and the singleton-lifting core are the same actual diagram. -/
theorem saturatedColumnCore_eq_tail (D : BetaDiagram (n + 3)) (hP : D.PositiveCorner) :
    D.saturatedColumnCore hP = (D.cornerDiagram hP).tail := by
  have hExt (A B : BetaDiagram (n + 1)) (hr : A.row = B.row) (hc : A.col = B.col) :
      A = B := by
    cases A
    cases B
    cases hr
    cases hc
    rfl
  apply hExt <;> funext i
  all_goals simp only [saturatedColumnCore, reindexOrder, suffix, tail, cornerDiagram]
  all_goals congr 1
  all_goals apply Fin.ext
  all_goals simp [Fin.natAdd, Fin.cast]
  all_goals omega

/-- No common beta entry is introduced by the actual core restriction. -/
theorem saturatedColumnCore_zeroFree (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hZ : D.ZeroFree) : (D.saturatedColumnCore hP).ZeroFree := by
  rw [saturatedColumnCore_eq_tail]
  intro i j
  exact hZ i.succ.succ j.succ.castSucc

/-- All four positive parameters and the parent motion are reconstructed,
with no supplied placement or normalization premise. -/
theorem saturated_column_singleton_context (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hSat : D.row 2 < D.col 0) :
    ∃ (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g),
      D.TranslationEquivalent
        ((D.saturatedColumnCore hP).singletonContext s u v g hs hu hv hg) := by
  rw [saturatedColumnCore_eq_tail]
  exact D.singleton_parent_of_first_cut hP hSat

/-- The source assumptions supply the entire geometric singleton context
and its connected zero-free core with at most two negatives. -/
theorem saturated_column_context_data (D : BetaDiagram (n + 3)) (hn : 3 ≤ n)
    (hD : D.Connected) (hZ : D.ZeroFree)
    (hSat : D.row 2 < D.col 0) (hBudget : negativeCount D ≤ n + 3) :
    let hP := D.positiveCorner_of_connected_zeroFree hD hZ
    (D.saturatedColumnCore hP).Connected ∧
      (D.saturatedColumnCore hP).ZeroFree ∧
      negativeCount (D.saturatedColumnCore hP) ≤ 2 ∧
      ∃ (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g),
        D.TranslationEquivalent
          ((D.saturatedColumnCore hP).singletonContext s u v g hs hu hv hg) := by
  dsimp only
  exact ⟨D.saturated_column_core_connected hn hD hZ hSat hBudget,
    D.saturatedColumnCore_zeroFree _ hZ,
    D.saturated_column_core_small hD hZ hSat hBudget,
    D.saturated_column_singleton_context _ hSat⟩

end SkewJacobiNegative.BetaDiagram
