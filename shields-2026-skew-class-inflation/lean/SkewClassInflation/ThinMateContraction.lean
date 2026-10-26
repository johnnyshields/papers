/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinTotalContraction
import SkewClassInflation.ThinBoundaryGaps
import SkewClassInflation.ZeroContractionBoundaries

/-!
# Produced total contractions and exterior orientations of arbitrary mates

Formalizes the total-contraction and global-orientation inputs of
`thm:two-row-thin-class` in `shields-2026-skew-class-inflation.tex`.
Both are derived from the original full Schur equality.  Unit-polynomial
observations, the contraction function, and exterior-gap positivity are
supplied by proved declarations, never by additional binders.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The actual padded zero-gap count is a coefficient of the complete gap multiset. -/
theorem zeroSeamCount_eq_count {n : ℕ} (P : Profile n) :
    zeroSeamCount P = P.gapMultiset.count 0 := by
  rw [zeroSeamCount, Gluing.Profile.gapMultiset, Multiset.count_map]
  change (∑ j : Fin n, if P.g j = 0 then 1 else 0) =
    (Finset.univ.filter (fun j : Fin n => 0 = P.g j)).card
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  simp only [eq_comm]

/-- Full polynomial equality gives equal zero-gap counts across arbitrary row counts. -/
theorem zeroSeamCount_eq_of_schur_eq {n m : ℕ} (P : Profile n) (Q : Profile m)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : zeroSeamCount P = zeroSeamCount Q := by
  have hn := Nat.succ.inj (P.toBetaDiagram.row_count_of_schur_eq Q.toBetaDiagram he)
  subst m
  rw [zeroSeamCount_eq_count, zeroSeamCount_eq_count]
  have hg := Gluing.Profile.gaps_eq_of_schur_eq
    (by simpa only [Gluing.Profile.toBetaDiagram_schur] using he)
  exact congrArg (Multiset.count 0) hg

namespace ThinParameters

variable (B : ThinParameters)

/-- The actual unit-polynomial source product is produced for every arbitrary connected mate. -/
theorem arbitrary_mate_constant {M k : ℕ} (α : Composition M) (hM : 0 < M) (Q : Profile k)
    (he : Q.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur) :
    (unitSchur Q).coeff 0 = (B.powerFunctions α.blocks (fun _m hm => α.blocks_pos hm)).prod := by
  rw [unitSchur_eq_of_schur_eq Q (B.diagram α hM).2 he, B.diagram_constant_coefficient]

/-- Every actual mate has a total contraction with the genuine full total-power function. -/
theorem arbitrary_mate_total_contraction {M k : ℕ} (α : Composition M) (hM : 0 < M)
    (Q : Profile k)
    (he : Q.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur) :
    (contractAllZeros Q).2.toBetaDiagram.schur = (B.innerPower M hM).toBetaDiagram.schur := by
  have hn := Nat.succ.inj
    (Q.toBetaDiagram.row_count_of_schur_eq (B.diagram α hM).2.toBetaDiagram he)
  subst k
  have hQ : Staircase.Thick Q := GeneralHessenberg.hessenberg_thick _
    (hessenberg_of_equal_schur (B.diagram α hM).2.toBetaDiagram Q.toBetaDiagram
      (B.diagram α hM).2.toBetaDiagram_connected Q.toBetaDiagram_connected he.symm
      (B.diagram_thick α hM).hessenberg)
  have hz := zeroSeamCount_eq_of_schur_eq Q (B.diagram α hM).2 he
  have hu := unitSchur_eq_of_schur_eq Q (B.diagram α hM).2 he
  have hc := congrArg (fun p : Polynomial CompleteRing => p.coeff (zeroSeamCount Q)) hu
  rw [zero_seam_highest_coefficient Q hQ, hz,
    zero_seam_highest_coefficient _ (B.diagram_thick α hM)] at hc
  have hs := mul_left_cancel₀
    (pow_ne_zero (zeroSeamCount (B.diagram α hM).2) (by norm_num : (-1 : CompleteRing) ≠ 0)) hc
  exact hs.trans (B.diagram_total_contraction α hM)

/-- The source block product and total contraction place the shortest row at a whole exterior. -/
theorem arbitrary_mate_exterior {M k : ℕ} (α : Composition M) (hM : 0 < M) (Q : Profile k)
    (he : Q.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur) :
    Q.r 0 = B.a ∨ Q.r (Fin.last k) = B.a := by
  have hn := Nat.succ.inj
    (Q.toBetaDiagram.row_count_of_schur_eq (B.diagram α hM).2.toBetaDiagram he)
  subst k
  have hQ : Staircase.Thick Q := GeneralHessenberg.hessenberg_thick _
    (hessenberg_of_equal_schur (B.diagram α hM).2.toBetaDiagram Q.toBetaDiagram
      (B.diagram α hM).2.toBetaDiagram_connected Q.toBetaDiagram_connected he.symm
      (B.diagram_thick α hM).hessenberg)
  let C := contractAllZeros Q
  have hc := B.arbitrary_mate_total_contraction α hM Q he
  have hconst := B.arbitrary_mate_constant α hM Q he
  let fs := B.powerFunctions α.blocks (fun _m hm => α.blocks_pos hm)
  have hfs : ∀ p ∈ fs, B.IsPowerFunction p :=
    B.powerFunctions_are_actual α.blocks (fun _m hm => α.blocks_pos hm)
  have hfirst := contractAllZeros_first_row Q hQ
    (B.first_gap_positive_of_product Q fs hfs hconst)
  have hlast := contractAllZeros_last_row Q hQ
    (B.last_gap_positive_of_product Q fs hfs hconst)
  have hmem : (C : ConnectedProfile) ∈
      ConnectedProfile.schurClass (⟨M, B.innerPower M hM⟩ : ConnectedProfile) := by
    change profileSchur C.2 = profileSchur (B.innerPower M hM)
    simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hc
  rw [B.innerPower_full_class M hM] at hmem
  rcases Set.mem_insert_iff.mp hmem with hC | hC
  · left
    have hr := congrArg (fun D : ConnectedProfile => D.2.r 0) hC
    change C.2.r 0 = (B.innerPower M hM).r 0 at hr
    have hs : (B.innerPower M hM).r 0 = B.a := rfl
    exact hfirst.symm.trans (hr.trans hs)
  · right
    have hr := congrArg (fun D : ConnectedProfile => D.2.r (Fin.last D.1))
      (Set.mem_singleton_iff.mp hC)
    change C.2.r (Fin.last C.1) = (B.innerPower M hM).rotate.r (Fin.last M) at hr
    have hs : (B.innerPower M hM).rotate.r (Fin.last M) = B.a := by
      change (B.innerPower M hM).r (Fin.last M).rev = B.a
      rw [Fin.rev_last]
      rfl
    exact hlast.symm.trans (hr.trans hs)

/-- One global rotation produces a genuine original mate whose first row is the shorter endpoint. -/
theorem arbitrary_mate_oriented {M k : ℕ} (α : Composition M) (hM : 0 < M) (Q : Profile k)
    (he : Q.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur) :
    ∃ R : Profile k, (R = Q ∨ R = Q.rotate) ∧ R.r 0 = B.a ∧
      R.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur := by
  rcases B.arbitrary_mate_exterior α hM Q he with hfirst | hlast
  · exact ⟨Q, Or.inl rfl, hfirst, he⟩
  · refine ⟨Q.rotate, Or.inr rfl, ?_, ?_⟩
    · change Q.r (0 : Fin (k + 1)).rev = B.a
      simpa only [Fin.rev_zero] using hlast
    · rw [Gluing.Profile.toBetaDiagram_schur, Gluing.Profile.schur_rotate,
        ← Gluing.Profile.toBetaDiagram_schur Q, he]

end ThinParameters
end SkewClassInflation
