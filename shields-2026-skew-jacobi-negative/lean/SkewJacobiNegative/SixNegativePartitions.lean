/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.ComponentBudget

/-!
# Self-conjugacy at six negatives

The distinctness clause of `thm:six-negative-minimum` follows from the actual
negative partition, without imposing any partition on a mate.
-/
namespace SkewJacobiNegative

private theorem positive_length_le_sum (l : List ℕ) (h : ∀ a ∈ l, 0 < a) :
    l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- The only self-conjugate positive partition of area six is the staircase. -/
theorem self_conjugate_six_eq_staircase (ρ : List ℕ) (hρ : IsNegativePartition ρ)
    (hSum : ρ.sum = 6) (hSelf : PartitionsConjugate ρ ρ) : ρ = [3, 2, 1] := by
  have hfilter : (ρ.filter fun r => 0 < r) = ρ := by
    apply List.filter_eq_self.mpr
    intro a ha
    simpa using hρ.2 a ha
  have hfirst := hSelf 0
  rw [hfilter] at hfirst
  cases ρ with
  | nil => simp at hSum
  | cons a l =>
    have hl := positive_length_le_sum l (fun b hb => hρ.2 b (by simp [hb]))
    simp only [List.getD_cons_zero, List.length_cons, List.sum_cons] at hfirst hSum
    have hlen : l.length ≤ 2 := by omega
    cases l with
    | nil => simp at hfirst hSum; omega
    | cons b l =>
      have hab := (List.pairwise_cons.mp hρ.1).1 b (by simp)
      cases l with
      | nil => simp at hfirst hSum; omega
      | cons c l =>
        cases l with
        | cons d l => simp at hlen
        | nil =>
          have hb := hρ.2 b (by simp)
          have hc := hρ.2 c (by simp)
          have hbc := (List.pairwise_cons.mp (List.pairwise_cons.mp hρ.1).2).1 c
            (by simp)
          simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
            Nat.add_zero] at hfirst hSum
          have ha : a = 3 := by omega
          have heB : b = 2 := by omega
          have heC : c = 1 := by omega
          simp [ha, heB, heC]

namespace BetaDiagram
variable {n : ℕ}

/-- At area six, a realization in at most five rows forces the complete staircase. -/
theorem six_partition_low_minimum (ρ : List ℕ) (hρ : IsNegativePartition ρ)
    (hSum : ρ.sum = 6) (hMin : minimumRealizingRows ρ ≤ 5) : ρ = [3, 2, 1] := by
  have hBounds := ((minimumRealizingRows_le_iff ρ 5).mp hMin).2
  cases ρ with
  | nil => simp at hSum
  | cons a l =>
    have ha := hBounds 0 (by simp)
    simp only [List.getD_cons_zero] at ha
    cases l with
    | nil => simp at hSum; omega
    | cons b l =>
      have hb := hBounds 1 (by simp)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hb
      cases l with
      | nil => simp at hSum; omega
      | cons c l =>
        have hc := hBounds 2 (by simp)
        simp only [List.getD_cons_succ, List.getD_cons_zero] at hc
        cases l with
        | nil =>
          simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hSum
          have heA : a = 3 := by omega
          have heB : b = 2 := by omega
          have heC : c = 1 := by omega
          simp [heA, heB, heC]
        | cons d l =>
          have hd := hBounds 3 (by simp)
          simp only [List.getD_cons_succ, List.getD_cons_zero] at hd
          have hp := hρ.2 d (by simp)
          omega

/-- A half-turn-symmetric actual board has a self-conjugate actual negative partition. -/
theorem symmetric_negative_partition_self_conjugate (D : BetaDiagram n)
    (hD : D.Symmetric) : PartitionsConjugate (negativePartition D) (negativePartition D) := by
  obtain ⟨c, hr, hc⟩ := hD
  have hm : negativePartition D.rotate = negativePartition D := by
    apply D.rotate.negativePartition_eq_of_mask_eq D
    intro i j
    have hri := hr i
    have hcj := hc j
    change -D.col i.rev < -D.row j.rev ↔ D.row i < D.col j
    omega
  simpa only [hm] using D.rotate_partition_conjugate

/-- The two motion representatives in the six-negative minimum stratum are distinct. -/
theorem six_negative_minimum_not_symmetric (D : BetaDiagram n)
    (hCount : negativeCount D = 6)
    (hMin : minimumRealizingRows (negativePartition D) = 6) : ¬ D.Symmetric := by
  intro hs
  have hp := self_conjugate_six_eq_staircase (negativePartition D)
    D.negativePartition_isPartition (D.negativePartition_sum.trans hCount)
    (D.symmetric_negative_partition_self_conjugate hs)
  rw [hp] at hMin
  have hm : minimumRealizingRows [3, 2, 1] = 5 := by decide
  omega

end BetaDiagram
end SkewJacobiNegative
