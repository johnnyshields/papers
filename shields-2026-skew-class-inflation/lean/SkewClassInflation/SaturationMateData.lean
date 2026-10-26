/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationPowers

/-!
# Produced constant-gap data for arbitrary general-power mates

The full-board reduction in `lem:merged-block-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Every connected mate, at an
arbitrary row count, is forced into the same constant-gap Hessenberg
domain.  This includes zero inner gaps.  The ribbon comparison is
assembled in `SaturationRibbonReduction`; the subsequent rigidity step
still requires the overlap-word bridge and ribbon factor-reversal
classification.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- All full-board geometric input data are produced from the original function equality. -/
theorem power_mate_reduction (m : ℕ) (hm : 0 < m) {n : ℕ} (Q : Profile n)
    (he : Q.toBetaDiagram.schur = (A.power m hm).toBetaDiagram.schur) :
    n = m * A.k ∧ Staircase.Thick Q ∧ (∀ j, Q.g j = A.c) ∧ ∀ i, A.d < Q.r i := by
  have hn := Nat.succ.inj
    (Q.toBetaDiagram.row_count_of_schur_eq (A.power m hm).toBetaDiagram he)
  change n = m * A.k at hn
  subst n
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact GeneralHessenberg.hessenberg_thick _
      (hessenberg_of_equal_schur (A.power m hm).toBetaDiagram Q.toBetaDiagram
        (A.power m hm).toBetaDiagram_connected Q.toBetaDiagram_connected he.symm
        (A.power_thick m hm).hessenberg)
  · have hg := Gluing.Profile.gaps_eq_of_schur_eq
      (by simpa only [Gluing.Profile.toBetaDiagram_schur] using he)
    intro j
    have hj : Q.g j ∈ Q.gapMultiset := Gluing.Profile.mem_gapMultiset.mpr ⟨j, rfl⟩
    rw [hg] at hj
    obtain ⟨i, hi⟩ := Gluing.Profile.mem_gapMultiset.mp hj
    exact hi.symm
  · have hr := (Gluing.Profile.rows_eq_of_schur_eq
      (by simpa only [Gluing.Profile.toBetaDiagram_schur] using he)).2
    intro i
    have hi : Q.r i ∈ Q.rowMultiset := Gluing.Profile.mem_rowMultiset.mpr ⟨i, rfl⟩
    rw [hr] at hi
    obtain ⟨j, hj⟩ := Gluing.Profile.mem_rowMultiset.mp hi
    rw [← hj]
    exact A.power_rows_above_seam m hm j

end SkewClassInflation.SaturationInner
