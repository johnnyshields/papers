/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.AffineHomogenization
import SkewJacobiNegative.FullBoardReadings
import SkewJacobiNegative.NonnegativeRigidity

/-!
# Schur classes and arbitrary-mate rigidity

Translation classes, rotation rigidity, and faithful Gamma descent for
`sec:introduction` and `lem:homogenization` of
`shields-2026-skew-jacobi-negative.tex`.  The comparison diagram's order is
quantified independently and then recovered from the actual Schur polynomial.
-/

namespace SkewJacobiNegative.BetaDiagram
variable {n m : ℕ}

/-- Literal translation or half-turn, after producing equality of row counts. -/
def MotionEquivalent (D : BetaDiagram n) (E : BetaDiagram m) : Prop :=
  ∃ h : n = m, D.TranslationEquivalent (E.castOrder h.symm) ∨
    D.RotationEquivalent (E.castOrder h.symm)

/-- Rotation rigidity against connected mates of every row count. -/
def RotationRigid (D : BetaDiagram n) : Prop :=
  ∀ m (E : BetaDiagram m), E.Connected → E.schur = D.schur → D.MotionEquivalent E

/-- Transport of an order index preserves actual connectedness. -/
theorem castOrder_connected (D : BetaDiagram n) (h : n = m) :
    (D.castOrder h).Connected ↔ D.Connected := by
  cases h
  rfl

/-- The same-order interface is justified by the proved row-count reading. -/
theorem rotationRigid_iff_same_order (D : BetaDiagram n) : D.RotationRigid ↔
    ∀ E : BetaDiagram n, E.Connected → E.schur = D.schur →
      D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  constructor
  · intro h E hE he
    obtain ⟨hn, hm⟩ := h n E hE he
    have hh : hn = rfl := Subsingleton.elim _ _
    rw [hh] at hm
    simpa only [castOrder] using hm
  · intro h m E hE he
    have hn : n = m := D.row_count_of_schur_eq E he.symm
    refine ⟨hn, ?_⟩
    exact h (E.castOrder hn.symm) ((E.castOrder_connected hn.symm).mpr hE)
      (by rw [castOrder_schur]; exact he)

/-- The already proved nonnegative theorem establishes the genuine class property. -/
theorem rotationRigid_of_nonnegative (D : BetaDiagram n)
    (hD : D.Connected) (hN : D.Nonnegative) : D.RotationRigid := by
  rw [D.rotationRigid_iff_same_order]
  intro E hE he
  exact D.nonnegative_rigidity_same_order E hD hE hN he.symm

/-- An arbitrary equal full-board mate is connected, by actual Schur irreducibility. -/
theorem connected_full_mate_of_schur_eq (D : BetaDiagram n) (E : BetaDiagram m)
    (hD : D.Connected) (he : D.schur = E.schur) : E.Connected := by
  have hn := D.row_count_of_schur_eq E he
  subst m
  exact D.connected_of_schur_eq E hD he

/-- Connected-mate rigidity therefore covers every full-board mate, including empty
and disconnected candidates without separate case hypotheses. -/
theorem RotationRigid.full_mate {D : BetaDiagram n} (hR : D.RotationRigid)
    (hD : D.Connected) (E : BetaDiagram m) (he : E.schur = D.schur) :
    D.MotionEquivalent E :=
  hR m E (D.connected_full_mate_of_schur_eq E hD he.symm) he

/-- Any same-order zero-free rigidity theorem descends to all connected full-board mates. -/
theorem gamma_zeroFree_rigidity_descends (D : BetaDiagram (n + 1))
    (hD : D.Connected)
    (hR : ∀ E : BetaDiagram (n + 1), E.Connected → E.ZeroFree →
      E.schur = D.gamma.schur → D.gamma.TranslationEquivalent E ∨
        D.gamma.RotationEquivalent E) : D.RotationRigid := by
  rw [D.rotationRigid_iff_same_order]
  intro E hE he
  have hpoly : E.gamma.schur = D.gamma.schur :=
    (E.gamma_schur_eq_iff_same_order D hE hD).mpr he
  obtain ht | hr := hR E.gamma ((E.gamma_connected_iff).mpr hE) E.gamma_zeroFree hpoly
  · exact Or.inl ((D.gamma_translation_iff E).mp ht)
  · exact Or.inr ((D.gamma_rotation_iff E).mp hr)

/-- The full rigidity property of the affine image implies the full source property. -/
theorem gamma_rigidity_descends (D : BetaDiagram (n + 1))
    (hD : D.Connected) (hR : D.gamma.RotationRigid) : D.RotationRigid := by
  apply D.gamma_zeroFree_rigidity_descends hD
  intro E hE _ he
  exact (D.gamma.rotationRigid_iff_same_order).mp hR E hE he

end SkewJacobiNegative.BetaDiagram
