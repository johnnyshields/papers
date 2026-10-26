/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FourRowBorders
import SkewJacobiNegative.FiveNegativeClassification
import SkewJacobiNegative.StaircaseHigherRows
import SkewJacobiNegative.SixNegativeMinimum
import SkewJacobiNegative.NegativeThreshold

/-!
# Classification through six negative entries

The complete alternatives of `thm:classification`, with independently quantified
mate row count, common beta entries, and the original exceptional parameter domains.
-/
namespace SkewJacobiNegative.BetaDiagram
variable {n m : ℕ}

private theorem small_order_negative_count (D : BetaDiagram n) (hD : D.Connected)
    (hn : n ≤ 4) : negativeCount D ≤ 3 := by
  classical
  let S : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.2.val + 1 < p.1.val
  have hs : negativeSites D ⊆ S := by
    intro p hp
    have hb := D.negative_lt_predecessor hD ((D.mem_negativeSites p.1 p.2).mp hp)
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hc : S.card ≤ 3 := by
    interval_cases n <;> decide
  exact (Finset.card_le_card hs).trans hc

/-- The only nonmotion mates below seven negatives belong to the stated seven families. -/
theorem classification_through_six (D : BetaDiagram n) (hD : D.Connected)
    (hCount : negativeCount D ≤ 6) (E : BetaDiagram m) (he : E.schur = D.schur) :
    D.MotionEquivalent E ∨
    (∃ hrowD : n = 4, ∃ hrowE : m = 4,
      ∃ hDC : (D.castOrder hrowD).Connected,
      ∃ hEC : (E.castOrder hrowE).Connected,
        negativeCount D = 3 ∧
        FourRowHessenberg.FamilyRelation ((D.castOrder hrowD).toProfile hDC)
          ((E.castOrder hrowE).toProfile hEC)) ∨
    (∃ hrowD : n = 5, ∃ hrowE : m = 5,
      negativeCount D = 5 ∧ ∃ P second,
        FiveNegative.ExceptionalMember P second (D.castOrder hrowD) ∧
        FiveNegative.ExceptionalMember P second (E.castOrder hrowE)) ∨
    (∃ hrowD : n = 5, ∃ hrowE : m = 5,
      ∃ hDC : (D.castOrder hrowD).Connected,
      ∃ hEC : (E.castOrder hrowE).Connected,
        negativeCount D = 6 ∧ ∃ X : StaircaseFivePlacements.Scheme,
          X.Member ((D.castOrder hrowD).toProfile hDC) ∧
          X.Member ((E.castOrder hrowE).toProfile hEC)) := by
  by_cases hlow : negativeCount D ≤ 4
  · rcases D.low_negative_complete_class hD hlow E he with hm | hf
    · exact Or.inl hm
    · exact Or.inr (Or.inl hf)
  have hn : 5 ≤ n := by
    by_contra hn
    have hc := small_order_negative_count D hD (by omega)
    omega
  have hE := D.connected_full_mate_of_schur_eq E hD he.symm
  by_cases h5 : negativeCount D = 5
  · rcases D.five_negative_full_classification hD h5 E he with hm | ⟨hd, he, P, s, hP, hQ⟩
    · exact Or.inl hm
    · exact Or.inr (Or.inr (Or.inl ⟨hd, he, h5, P, s, hP, hQ⟩))
  have h6 : negativeCount D = 6 := by omega
  by_cases hMin : minimumRealizingRows (negativePartition D) ≤ 5
  · have hρ := six_partition_low_minimum (negativePartition D)
      D.negativePartition_isPartition (D.negativePartition_sum.trans h6) hMin
    by_cases hn5 : n = 5
    · subst n
      have hm5 : m = 5 := E.row_count_of_schur_eq D he
      subst m
      rcases StaircaseHigherRows.staircase_partition_base D hD hρ with hr | ⟨X,hX,hClass⟩
      · exact Or.inl (hr.full_mate hD E he)
      · have hpoly : D.schur = (E.toProfile hE).toBetaDiagram.schur := by
          rw [Gluing.Profile.toBetaDiagram_schur, E.toProfile_schur hE]
          exact he.symm
        exact Or.inr (Or.inr (Or.inr
          ⟨rfl, rfl, hD, hE, h6, X, hX, (hClass _).mp hpoly⟩))
    · exact Or.inl ((StaircaseHigherRows.partition_higher_rows D (by omega) hD hρ).full_mate
        hD E he)
  · by_cases hMin6 : minimumRealizingRows (negativePartition D) = 6
    · exact Or.inl (D.six_negative_minimum_full_class hD h6 hMin6 E he)
    · exact Or.inl (D.negative_threshold_full_class hD (by omega) (by omega) E he)

end SkewJacobiNegative.BetaDiagram
