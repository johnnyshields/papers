/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FiveBorderExclusion

/-!
# Complete five-negative classes

The five-negative clause of `thm:classification`, including common beta entries
and independently quantified full-board mates.  The base classification and
higher-row rigidity supply every alternative without additional proof inputs.
-/
namespace SkewJacobiNegative.BetaDiagram

private theorem five_negative_source_order {n : ℕ} (D : BetaDiagram n)
    (hD : D.Connected) (hν : negativeCount D = 5) : 5 ≤ n := by
  classical
  by_contra hn
  have hn4 : n ≤ 4 := by omega
  let S : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.2.val + 1 < p.1.val
  have hs : negativeSites D ⊆ S := by
    intro p hp
    have hb := D.negative_lt_predecessor hD ((D.mem_negativeSites p.1 p.2).mp hp)
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hc : S.card ≤ 3 := by interval_cases n <;> decide
  have hcount := Finset.card_le_card hs
  change negativeCount D ≤ S.card at hcount
  omega

/-- Every nonmotion five-negative mate belongs to the same displayed quartet. -/
theorem five_negative_full_classification {n m : ℕ} (D : BetaDiagram n)
    (hD : D.Connected) (hν : negativeCount D = 5) (E : BetaDiagram m)
    (he : E.schur = D.schur) :
    D.MotionEquivalent E ∨
      ∃ hrowD : n = 5, ∃ hrowE : m = 5,
        ∃ P second, FiveNegative.ExceptionalMember P second (D.castOrder hrowD) ∧
          FiveNegative.ExceptionalMember P second (E.castOrder hrowE) := by
  have hn := five_negative_source_order D hD hν
  by_cases hn5 : n = 5
  · subst n
    have hE := D.connected_full_mate_of_schur_eq E hD he.symm
    have hm5 : m = 5 := E.row_count_of_schur_eq D he
    subst m
    rcases (FiveNegative.five_base_pair D E hD hE hν).mp he.symm with ho | hf
    · exact Or.inl ⟨rfl, ho⟩
    · exact Or.inr ⟨rfl, rfl, hf⟩
  · exact Or.inl ((FiveExceptional.five_higher_rigidity D (by omega) hD hν).full_mate
      hD E he)

/-- The exact exceptional class, with no connectedness premise on the mate. -/
theorem five_exceptional_full_class {m : ℕ} (P : FiveExceptional.Parameters)
    (second : Bool) (D : BetaDiagram 5) (hD : D.Connected)
    (hmem : FiveNegative.ExceptionalMember P second D) (E : BetaDiagram m) :
    D.schur = E.schur ↔
      ∃ hrow : m = 5, FiveNegative.ExceptionalMember P second (E.castOrder hrow) := by
  constructor
  · intro he
    have hE := D.connected_full_mate_of_schur_eq E hD he
    exact (FiveNegative.five_base_complete_class P second D hD hmem E hE).mp he
  · rintro ⟨hrow, hE⟩
    have hh := (FiveNegative.exceptional_member_schur P second D hmem).trans
      (FiveNegative.exceptional_member_schur P second (E.castOrder hrow) hE).symm
    simpa only [castOrder_schur] using hh

end SkewJacobiNegative.BetaDiagram
