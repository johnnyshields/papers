/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.SaturatedColumnContext
import SkewJacobiNegative.LowNegativePatterns

/-!
# Rigidity from a saturated negative column

The full arbitrary-mate conclusion of `thm:saturated-column`.  The actual
core and its fixed leader are produced from saturation.  Gamma transport
retains common beta entries, with no endpoint-extension rigidity premise.
-/
namespace SkewJacobiNegative.BetaDiagram
variable {n : ℕ}

/-- Singleton lifting consumes the entire actual core data produced by saturation. -/
theorem saturated_column_zeroFree_rigidity (D : BetaDiagram (n + 6))
    (hD : D.Connected) (hZ : D.ZeroFree)
    (hSat : D.row 2 < D.col 0) (hBudget : negativeCount D ≤ n + 6) :
    D.RotationRigid := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let Q : BetaDiagram (n + 4) := D.saturatedColumnCore hP
  have hdata := D.saturated_column_context_data (by omega) hD hZ hSat hBudget
  change Q.Connected ∧ Q.ZeroFree ∧ negativeCount Q ≤ 2 ∧
    ∃ (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g),
      D.TranslationEquivalent (Q.singletonContext s u v g hs hu hv hg) at hdata
  obtain ⟨hQ, hZQ, hcount, s, u, v, g, hs, hu, hv, hg, hmotion⟩ := hdata
  have hrigid : (Q.singletonContext s u v g hs hu hv hg).RotationRigid :=
    Q.singletonContext_rotationRigid hQ hZQ (Q.two_negative_rigidity hQ hcount)
      (Q.endpointLeader_two_negative_ge_four hQ hZQ hcount) s u v g hs hu hv hg
  rw [D.rotationRigid_iff_same_order]
  intro E hE he
  have hparent := (Q.singletonContext s u v g hs hu hv hg).rotationRigid_iff_same_order.mp
    hrigid E hE (he.trans hmotion.schur_eq)
  obtain ⟨c, hrows, hcols⟩ := hmotion
  rcases hparent with ⟨d, hr, hc⟩ | ⟨d, hr, hc⟩
  · left
    refine ⟨d + c, ?_, ?_⟩ <;> intro i
    · have h1 := hrows i
      have h2 := hr i
      omega
    · have h1 := hcols i
      have h2 := hc i
      omega
  · right
    refine ⟨d + c, ?_, ?_⟩ <;> intro i
    · have h1 := hrows i
      have h2 := hr i
      omega
    · have h1 := hcols i
      have h2 := hc i
      omega

/-- Faithful affine transport removes no full-board source from the theorem. -/
theorem saturated_column_oriented_rigidity (D : BetaDiagram (n + 6))
    (hD : D.Connected) (hSat : D.row 2 < D.col 0)
    (hBudget : negativeCount D ≤ n + 6) : D.RotationRigid := by
  apply D.gamma_rigidity_descends hD
  apply D.gamma.saturated_column_zeroFree_rigidity
    (D.gamma_connected_iff.mpr hD) D.gamma_zeroFree
    ((D.gamma_negative_iff 2 0).mpr hSat)
  simpa only [gamma_negativeCount] using hBudget

/-- Either permitted orientation gives the same full source conclusion. -/
theorem saturated_column_rigidity (D : BetaDiagram (n + 6)) (hD : D.Connected)
    (hSat : D.row 2 < D.col 0 ∨ D.rotate.row 2 < D.rotate.col 0)
    (hBudget : negativeCount D ≤ n + 6) : D.RotationRigid := by
  rcases hSat with h | h
  · exact D.saturated_column_oriented_rigidity hD h hBudget
  · have hrot := D.rotate.saturated_column_oriented_rigidity (D.rotate_connected hD) h
      (by
        rw [D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur]
        exact hBudget)
    rw [D.rotationRigid_iff_same_order]
    intro E hE he
    have hpair := D.rotate.rotationRigid_iff_same_order.mp hrot E.rotate
      (E.rotate_connected hE) (by simpa only [rotate_schur] using he)
    rcases hpair with ⟨c, hr, hc⟩ | ⟨c, hr, hc⟩
    · left
      refine ⟨-c, ?_, ?_⟩ <;> intro i
      · have h := hc i.rev
        simp only [rotate, Fin.rev_rev] at h
        omega
      · have h := hr i.rev
        simp only [rotate, Fin.rev_rev] at h
        omega
    · right
      refine ⟨-c, ?_, ?_⟩ <;> intro i
      · have h := hc i.rev
        simp only [rotate, Fin.rev_rev] at h
        omega
      · have h := hr i.rev
        simp only [rotate, Fin.rev_rev] at h
        omega

/-- Actual row count at least six, with no order or connectedness assumption on the mate. -/
theorem saturated_column_full_class (D : BetaDiagram n) (hn : 6 ≤ n)
    (hD : D.Connected)
    (hSat : D.row ⟨2, by omega⟩ < D.col ⟨0, by omega⟩ ∨
      D.rotate.row ⟨2, by omega⟩ < D.rotate.col ⟨0, by omega⟩)
    (hBudget : negativeCount D ≤ n) {m : ℕ} (E : BetaDiagram m)
    (he : E.schur = D.schur) : D.MotionEquivalent E := by
  rcases n with _ | (_ | (_ | (_ | (_ | (_ | n)))))
  all_goals try omega
  have hR : D.RotationRigid := D.saturated_column_rigidity hD hSat hBudget
  exact hR.full_mate hD E he

end SkewJacobiNegative.BetaDiagram
