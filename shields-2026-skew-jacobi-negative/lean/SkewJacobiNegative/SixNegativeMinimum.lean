/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.SaturatedColumnRigidity
import SkewJacobiNegative.SixNegativePartitions

/-!
# Rigidity at the six-negative minimum

The full two-orbit conclusion of `thm:six-negative-minimum`.  Actual six-row
cuts provide the base, connected bordering closes higher rows, and Gamma
transport includes common beta entries.  The negative partition proves
that the two motion representatives are distinct.
-/
namespace SkewJacobiNegative.BetaDiagram

variable {n : ℕ}

private theorem dense_of_zeroFree_count_zero {n : ℕ} (D : BetaDiagram n)
    (hZ : D.ZeroFree) (hCount : negativeCount D = 0) : D.Dense := by
  intro i j
  have hne := hZ i j
  have hn : ¬ D.row i < D.col j := by
    intro h
    have hp : 0 < negativeCount D := Finset.card_pos.mpr
      ⟨(i,j), (D.mem_negativeSites i j).mpr h⟩
    omega
  omega

/-- The middle two-plus-three cut has zero internal budget in both actual factors. -/
theorem six_negative_two_three_cut_rigidity (D : BetaDiagram 6)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D = 6)
    (hCut : D.row 3 < D.col 1) : D.RotationRigid := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let C : BetaDiagram (2 + 3) := D.twoCutCore (p := 1) (r := 2) hP
  let Q : BetaDiagram 2 := C.betaPrefix
  let R : BetaDiagram 3 := C.suffix
  have hcut : C.row 2 < C.col 1 := hCut
  have hCCount : negativeCount C = 6 := by
    change negativeCount (D.twoCutCore (p := 1) (r := 2) hP) = 6
    rw [twoCutCore, reindexOrder_negativeCount, D.corner_negativeCount hP]
    exact hCount
  have hbudget := negativeCount_at_cut (a := 2) (b := 3) C
    (by decide) (by decide) hcut
  have hQCount : negativeCount Q = 0 := by dsimp [Q]; omega
  have hRCount : negativeCount R = 0 := by dsimp [R]; omega
  have hZQ : Q.ZeroFree := by
    intro i j
    exact hZ (i.castAdd 3).succ (j.castAdd 3).castSucc
  have hZR : R.ZeroFree := by
    intro i j
    exact hZ (i.natAdd 2).succ (j.natAdd 2).castSucc
  have hDQ := dense_of_zeroFree_count_zero Q hZQ hQCount
  have hDR := dense_of_zeroFree_count_zero R hZR hRCount
  obtain ⟨hg, hmotion⟩ := D.parent_twoComponentContext_of_cut (p := 1) (r := 2) hP hcut
  exact D.rotationRigid_of_translation _ hmotion
    (Q.twoComponentContext_rotationRigid_of_dense R hDQ hDR D.topMargin D.bottomMargin
      (Q.col (Fin.last 1) - R.row 0) D.topMargin_pos D.bottomMargin_pos hg)

/-- The source's actual minimum-order child has only the two admissible cut sizes. -/
theorem six_negative_minimum_zeroFree_base (D : BetaDiagram 6)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D = 6)
    (hMin : minimumRealizingRows (negativePartition D) = 6) : D.RotationRigid := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let C := D.cornerDiagram hP
  have hNC : ¬ C.Connected := (D.corner_disconnected_iff_minimum hD hP).mpr hMin.symm
  obtain ⟨i,hi,hcut⟩ := C.exists_negative_cut (by decide) hNC
  have hbound : i.val ≤ 3 := by omega
  interval_cases hv : i.val
  · have he : i = (0 : Fin 5) := Fin.ext hv
    subst i
    apply D.saturated_column_rigidity hD (Or.inl hcut)
    omega
  · have he : i = (1 : Fin 5) := Fin.ext hv
    subst i
    exact D.six_negative_two_three_cut_rigidity hD hZ hCount hcut
  · have he : i = (2 : Fin 5) := Fin.ext hv
    subst i
    have hRotCount : negativeCount D.rotate = 6 :=
      (D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur).trans hCount
    have hRotZ : D.rotate.ZeroFree := by
      intro a b hab
      apply hZ b.rev a.rev
      change -D.col a.rev = -D.row b.rev at hab
      omega
    have hRotCut : D.rotate.row 3 < D.rotate.col 1 := by
      change -D.col 2 < -D.row 4
      exact neg_lt_neg hcut
    have hr := D.rotate.six_negative_two_three_cut_rigidity
      (D.rotate_connected hD) hRotZ hRotCount hRotCut
    apply D.rotationRigid_iff_same_order.mpr
    intro E hE he
    have hm := D.rotate.rotationRigid_iff_same_order.mp hr E.rotate
      (E.rotate_connected hE) (by simpa only [rotate_schur] using he)
    rcases hm with ⟨c, hrows, hcols⟩ | ⟨c, hrows, hcols⟩
    · left
      refine ⟨-c, ?_, ?_⟩ <;> intro j
      · have h := hcols j.rev
        simp only [rotate, Fin.rev_rev] at h
        omega
      · have h := hrows j.rev
        simp only [rotate, Fin.rev_rev] at h
        omega
    · right
      refine ⟨-c, ?_, ?_⟩ <;> intro j
      · have h := hcols j.rev
        simp only [rotate, Fin.rev_rev] at h
        omega
      · have h := hrows j.rev
        simp only [rotate, Fin.rev_rev] at h
        omega
  · have he : i = (3 : Fin 5) := Fin.ext hv
    subst i
    have hRotCut : D.rotate.row 2 < D.rotate.col 0 := by
      change -D.col 3 < -D.row 5
      exact neg_lt_neg hcut
    apply D.saturated_column_rigidity hD (Or.inr hRotCut)
    omega

/-- Above the minimum, connected bordering preserves this stratum and closes the induction. -/
theorem six_negative_minimum_zeroFree_rigidity (D : BetaDiagram n)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D = 6)
    (hMin : minimumRealizingRows (negativePartition D) = 6) : D.RotationRigid := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := D.connected_iff_minimumRealizingRows_le.mp hD
    rw [hMin] at hn
    by_cases h6 : n = 6
    · subst n
      exact D.six_negative_minimum_zeroFree_base hD hZ hCount hMin
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      let hP := D.positiveCorner_of_connected_zeroFree hD hZ
      let C := D.cornerDiagram hP
      have hC : C.Connected := (D.corner_connected_iff_above_minimum hP).mpr (by omega)
      have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
      have hCC : negativeCount C = 6 := by
        rw [D.corner_negativeCount hP]
        exact hCount
      have hCM : minimumRealizingRows (negativePartition C) = 6 := by
        rw [D.corner_negativePartition hP]
        exact hMin
      apply D.connected_border_rigidity hD hP hC
      · exact ih (k + 6) (by omega) C hC hCZ hCC hCM
      · intro t ht
        apply ih (k + 6) (by omega) (C.extendTop t ht)
          (C.extendTop_connected hC t ht) (C.extendTop_zeroFree hCZ t ht)
        · simpa only [extendTop_negativeCount] using hCC
        · simpa only [extendTop_negativePartition] using hCM

/-- Full-board rigidity in `thm:six-negative-minimum`, including common beta entries. -/
theorem six_negative_minimum_rigidity (D : BetaDiagram n)
    (hD : D.Connected) (hCount : negativeCount D = 6)
    (hMin : minimumRealizingRows (negativePartition D) = 6) : D.RotationRigid := by
  cases n with
  | zero => exact False.elim (by simpa [Connected] using hD.1)
  | succ n =>
    apply D.gamma_rigidity_descends hD
    apply D.gamma.six_negative_minimum_zeroFree_rigidity
      ((D.gamma_connected_iff).mpr hD) D.gamma_zeroFree
    · simpa only [gamma_negativeCount] using hCount
    · simpa only [gamma_negative_partition] using hMin

/-- No connectedness, row-count, or negative-mask premise is imposed on the mate. -/
theorem six_negative_minimum_full_class (D : BetaDiagram n)
    (hD : D.Connected) (hCount : negativeCount D = 6)
    (hMin : minimumRealizingRows (negativePartition D) = 6)
    {m : ℕ} (E : BetaDiagram m) (he : E.schur = D.schur) : D.MotionEquivalent E :=
  (D.six_negative_minimum_rigidity hD hCount hMin).full_mate hD E he

/-- The complete two-orbit conclusion of `thm:six-negative-minimum`. -/
theorem six_negative_minimum_classification (D : BetaDiagram n)
    (hD : D.Connected) (hCount : negativeCount D = 6)
    (hMin : minimumRealizingRows (negativePartition D) = 6) :
    D.RotationRigid ∧ ¬ D.Symmetric :=
  ⟨D.six_negative_minimum_rigidity hD hCount hMin,
    D.six_negative_minimum_not_symmetric hCount hMin⟩

end SkewJacobiNegative.BetaDiagram
