/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.ConnectedBorderRigidity
import SkewJacobiNegative.SaturatedColumnGeometry
import SkewJacobiNegative.SmallRowRigidity

/-!
# Uniform rigidity with at most one negative entry

The one-negative subcase of `thm:two-negatives` in
`shields-2026-skew-jacobi-negative.tex`.  Component budgets make every
larger child connected, and faithful affine transport retains common betas.
-/

namespace SkewJacobiNegative.BetaDiagram
variable {n : ℕ}

/-- Extending the largest row beta cannot introduce a common beta entry. -/
theorem extendTop_zeroFree (D : BetaDiagram (n + 1)) (hZ : D.ZeroFree)
    (t : ℤ) (ht : 0 < t) : (D.extendTop t ht).ZeroFree := by
  intro i j he
  by_cases hi : i = 0
  · subst i
    have hc := D.col_strictAnti.antitone (Fin.zero_le j)
    have hr := D.row_nonempty 0
    change (if (0 : Fin (n + 1)) = 0 then D.row 0 + t else D.row 0) = D.col j at he
    simp only [ite_true] at he
    omega
  · exact hZ i j (by simpa only [extendTop, ite_eq_right hi] using he)

/-- Extending the smallest column beta likewise preserves zero-freeness. -/
theorem extendBottom_zeroFree (D : BetaDiagram (n + 1)) (hZ : D.ZeroFree)
    (t : ℤ) (ht : 0 < t) : (D.extendBottom t ht).ZeroFree := by
  intro i j he
  by_cases hj : j = Fin.last n
  · subst j
    have hr := D.row_strictAnti.antitone (Fin.le_last i)
    have hc := D.row_nonempty (Fin.last n)
    change D.row i = (if Fin.last n = Fin.last n then D.col (Fin.last n) - t else
      D.col (Fin.last n)) at he
    simp only [ite_true] at he
    omega
  · exact hZ i j (by simpa only [extendBottom, ite_eq_right hj] using he)

/-- Positive endpoint shifts preserve the full negative count. -/
theorem extendTop_negativeCount (D : BetaDiagram (n + 1)) (t : ℤ) (ht : 0 < t) :
    negativeCount (D.extendTop t ht) = negativeCount D := by
  rw [← negativePartition_sum, extendTop_negativePartition, negativePartition_sum]

/-- The bottom shift has the same full-board count preservation. -/
theorem extendBottom_negativeCount (D : BetaDiagram (n + 1)) (t : ℤ) (ht : 0 < t) :
    negativeCount (D.extendBottom t ht) = negativeCount D := by
  rw [← negativePartition_sum, extendBottom_negativePartition, negativePartition_sum]

/-- The actual negative partition, including every zero-free Gamma row, is unchanged. -/
@[simp] theorem gamma_negative_partition (D : BetaDiagram n) :
    negativePartition D.gamma = negativePartition D :=
  D.gamma.negativePartition_eq_of_mask_eq D D.gamma_negative_iff

/-- Faithful affine homogenization preserves the full count, not only its bound. -/
theorem gamma_negativeCount (D : BetaDiagram n) : negativeCount D.gamma = negativeCount D := by
  rw [← negativePartition_sum, D.gamma.negativePartition_eq_of_mask_eq D D.gamma_negative_iff,
    negativePartition_sum]

/-- Induction on actual row count with a genuine connected child at every large step. -/
theorem one_negative_zeroFree_rigidity (D : BetaDiagram n) (hD : D.Connected)
    (hZ : D.ZeroFree) (hCount : negativeCount D ≤ 1) : D.RotationRigid := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 3
    · apply (rotationRigid_iff_same_order D).mpr
      intro E hE he
      exact D.small_rows_rigidity_same_order E hD hE hn he.symm
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      let hP := D.positiveCorner_of_connected_zeroFree hD hZ
      let C := D.cornerDiagram hP
      have hCCount : negativeCount C ≤ 1 := by
        rw [show negativeCount C = negativeCount D from D.corner_negativeCount hP]
        exact hCount
      have hC : C.Connected := connected_of_negativeCount_small C (by omega) (by omega)
      have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
      apply D.connected_border_rigidity hD hP hC
      · exact ih (k + 2) (by omega) C hC hCZ hCCount
      · intro t ht
        apply ih (k + 2) (by omega) (C.extendTop t ht)
        · exact C.extendTop_connected hC t ht
        · exact C.extendTop_zeroFree hCZ t ht
        · rw [extendTop_negativeCount]
          exact hCCount

/-- Every connected full board with at most one negative is rigid against arbitrary mates. -/
theorem one_negative_rigidity (D : BetaDiagram n) (hD : D.Connected)
    (hCount : negativeCount D ≤ 1) : D.RotationRigid := by
  cases n with
  | zero => exact False.elim (by simpa [Connected] using hD.1)
  | succ n =>
    apply D.gamma_rigidity_descends hD
    apply D.gamma.one_negative_zeroFree_rigidity ((D.gamma_connected_iff).mpr hD)
      D.gamma_zeroFree
    simpa only [gamma_negativeCount] using hCount

/-- The one-negative subcase imposes no connectedness or order restriction on the mate. -/
theorem one_negative_full_class (D : BetaDiagram n) (hD : D.Connected)
    (hCount : negativeCount D ≤ 1) {m : ℕ} (E : BetaDiagram m)
    (he : E.schur = D.schur) : D.MotionEquivalent E :=
  (D.one_negative_rigidity hD hCount).full_mate hD E he

end SkewJacobiNegative.BetaDiagram
