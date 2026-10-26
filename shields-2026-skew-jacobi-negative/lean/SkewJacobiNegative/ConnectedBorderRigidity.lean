/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.BorderCoefficients
import SkewJacobiNegative.SchurClasses

/-!
# Connected-child border rigidity

The connected-child clause of `lem:border` in
`shields-2026-skew-jacobi-negative.tex`, with arbitrary connected mates.
No nonnegative-index hypothesis is imposed on either full board.
-/

namespace SkewJacobiNegative.BetaDiagram
variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- A strict margin swap compares actual opposite endpoint extensions. -/
theorem connected_extensions_eq_of_swapped_margins (D E : BetaDiagram (n + 3))
    (hD : D.Connected) (hE : E.Connected)
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (hcore : (D.cornerDiagram hPD).TranslationEquivalent (E.cornerDiagram hPE))
    (ht : D.topMargin = E.bottomMargin) (hb : D.bottomMargin = E.topMargin)
    (hne : D.topMargin ≠ D.bottomMargin) (he : D.schur = E.schur) :
    let d := min D.topMargin D.bottomMargin
    let hd : 0 < d := lt_min D.topMargin_pos D.bottomMargin_pos
    ((D.cornerDiagram hPD).extendTop d hd).schur =
      ((D.cornerDiagram hPD).extendBottom d hd).schur := by
  classical
  have hl := D.largestLabel_eq_of_schur_eq E hD hE he
  let ND : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let NE : ℕ+ := ⟨E.largestLabel.toNat, by have := E.largestLabel_pos; omega⟩
  have hNDE : ND = NE := by
    apply Subtype.ext
    exact congrArg Int.toNat hl
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hEt : E.bottomMargin < E.topMargin := by omega
    have hEp : 0 < E.largestLabel - E.bottomMargin := by
      have hp := E.rotate.exterior_top_label_pos
      rw [E.rotate_largestLabel, E.rotate_topMargin] at hp
      exact hp
    let MD : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
      by have := D.exterior_top_label_pos; omega⟩
    let ME : ℕ+ := ⟨(E.largestLabel - E.bottomMargin).toNat, by omega⟩
    have hMDE : MD = ME := by
      apply Subtype.ext
      change (D.largestLabel - D.topMargin).toNat = (E.largestLabel - E.bottomMargin).toNat
      rw [hl, ht]
    have hDcoef : MvPolynomial.pderiv MD (eraseGenerator ND D.schur) =
        (-1) ^ (n + 3) * ((D.cornerDiagram hPD).extendTop D.topMargin D.topMargin_pos).schur :=
      D.border_top_coefficient hPD hlt
    have hEcoef : MvPolynomial.pderiv ME (eraseGenerator NE E.schur) =
        (-1) ^ (n + 3) *
          ((E.cornerDiagram hPE).extendBottom E.bottomMargin E.bottomMargin_pos).schur :=
      E.border_bottom_coefficient hPE hEt
    have hcoeff : (-1 : CompleteRing) ^ (n + 3) *
        ((D.cornerDiagram hPD).extendTop D.topMargin D.topMargin_pos).schur =
        (-1 : CompleteRing) ^ (n + 3) *
        ((E.cornerDiagram hPE).extendBottom E.bottomMargin E.bottomMargin_pos).schur := by
      calc
        _ = MvPolynomial.pderiv MD (eraseGenerator ND D.schur) := hDcoef.symm
        _ = MvPolynomial.pderiv MD (eraseGenerator ND E.schur) :=
          congrArg (fun p : CompleteRing => MvPolynomial.pderiv MD (eraseGenerator ND p)) he
        _ = MvPolynomial.pderiv ME (eraseGenerator NE E.schur) := by rw [hMDE, hNDE]
        _ = _ := hEcoef
    have heExt := mul_left_cancel₀
      (pow_ne_zero (n + 3) (neg_ne_zero.mpr (one_ne_zero : (1 : CompleteRing) ≠ 0))) hcoeff
    have hBot := extendBottom_schur_eq_of_translation
      (D.cornerDiagram hPD) (E.cornerDiagram hPE) hcore
      E.bottomMargin E.bottomMargin_pos
    dsimp only
    simpa only [min_eq_left hlt.le, ← ht] using heExt.trans hBot.symm
  · have hEt : E.topMargin < E.bottomMargin := by omega
    have hDp : 0 < D.largestLabel - D.bottomMargin := by
      have hp := D.rotate.exterior_top_label_pos
      rw [D.rotate_largestLabel, D.rotate_topMargin] at hp
      exact hp
    let MD : ℕ+ := ⟨(D.largestLabel - D.bottomMargin).toNat, by omega⟩
    let ME : ℕ+ := ⟨(E.largestLabel - E.topMargin).toNat,
      by have := E.exterior_top_label_pos; omega⟩
    have hMDE : MD = ME := by
      apply Subtype.ext
      change (D.largestLabel - D.bottomMargin).toNat = (E.largestLabel - E.topMargin).toNat
      rw [hl, hb]
    have hDcoef : MvPolynomial.pderiv MD (eraseGenerator ND D.schur) =
        (-1) ^ (n + 3) *
          ((D.cornerDiagram hPD).extendBottom D.bottomMargin D.bottomMargin_pos).schur :=
      D.border_bottom_coefficient hPD hgt
    have hEcoef : MvPolynomial.pderiv ME (eraseGenerator NE E.schur) =
        (-1) ^ (n + 3) * ((E.cornerDiagram hPE).extendTop E.topMargin E.topMargin_pos).schur :=
      E.border_top_coefficient hPE hEt
    have hcoeff : (-1 : CompleteRing) ^ (n + 3) *
        ((D.cornerDiagram hPD).extendBottom D.bottomMargin D.bottomMargin_pos).schur =
        (-1 : CompleteRing) ^ (n + 3) *
        ((E.cornerDiagram hPE).extendTop E.topMargin E.topMargin_pos).schur := by
      calc
        _ = MvPolynomial.pderiv MD (eraseGenerator ND D.schur) := hDcoef.symm
        _ = MvPolynomial.pderiv MD (eraseGenerator ND E.schur) :=
          congrArg (fun p : CompleteRing => MvPolynomial.pderiv MD (eraseGenerator ND p)) he
        _ = MvPolynomial.pderiv ME (eraseGenerator NE E.schur) := by rw [hMDE, hNDE]
        _ = _ := hEcoef
    have heExt := mul_left_cancel₀
      (pow_ne_zero (n + 3) (neg_ne_zero.mpr (one_ne_zero : (1 : CompleteRing) ≠ 0))) hcoeff
    have hTop := extendTop_schur_eq_of_translation
      (D.cornerDiagram hPD) (E.cornerDiagram hPE) hcore
      E.topMargin E.topMargin_pos
    dsimp only
    simpa only [min_eq_right hgt.le, ← hb] using hTop.trans heExt.symm

/-- Connectedness of an equal mate's actual corner follows from irreducibility. -/
theorem connected_corner_of_corner_eq (D E : BetaDiagram (n + 3))
    (hD : D.Connected) (hE : E.Connected) (hPD : D.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected) (he : D.schur = E.schur) :
    let hPE := D.positiveCorner_of_cornerPolynomial_eq E hD hE hPD
      (D.cornerPolynomial_eq_of_schur_eq E hD hE he)
    (E.cornerDiagram hPE).Connected := by
  dsimp only
  apply connected_of_schur_irreducible _ (by omega)
  rw [cornerDiagram_schur, ← D.cornerPolynomial_eq_of_schur_eq E hD hE he,
    ← D.cornerDiagram_schur hPD]
  exact (D.cornerDiagram hPD).schur_irreducible hCD

/-- A connected child and its endpoint rigidity settle aligned parents. -/
theorem connected_border_aligned_rigidity (D E : BetaDiagram (n + 3))
    (hD : D.Connected) (hE : E.Connected)
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected)
    (hCE : (E.cornerDiagram hPE).Connected)
    (hcore : (D.cornerDiagram hPD).TranslationEquivalent (E.cornerDiagram hPE))
    (hEndpoint : ∀ (t : ℤ) (ht : 0 < t),
      ((D.cornerDiagram hPD).extendTop t ht).schur =
        ((D.cornerDiagram hPD).extendBottom t ht).schur →
        (D.cornerDiagram hPD).Symmetric)
    (he : D.schur = E.schur) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  have hsum := D.marginSum_eq_of_corner_translation E hPD hPE hcore
    (D.largestLabel_eq_of_schur_eq E hD hE he)
  have hmin := D.border_minMargin_eq_of_schur_eq E hD hE hPD hPE hCD hCE he
  have hmargins :
      (D.topMargin = E.topMargin ∧ D.bottomMargin = E.bottomMargin) ∨
      (D.topMargin = E.bottomMargin ∧ D.bottomMargin = E.topMargin) := by
    omega
  rcases hmargins with ⟨ht, hb⟩ | ⟨ht, hb⟩
  · exact Or.inl (D.translation_of_corner_translation_of_margins E hPD hPE hcore ht hb)
  · by_cases hne : D.topMargin = D.bottomMargin
    · left
      apply D.translation_of_corner_translation_of_margins E hPD hPE hcore <;> omega
    · right
      apply D.rotation_of_corner_translation_of_swapped_margins E hPD hPE hcore ht hb
      exact hEndpoint _ _ (D.connected_extensions_eq_of_swapped_margins
        E hD hE hPD hPE hcore ht hb hne he)

/-- Endpoint isolation suffices; the endpoint extensions need not themselves be rigid. -/
theorem connected_border_endpoint_isolation_same_order (D E : BetaDiagram (n + 3))
    (hD : D.Connected) (hE : E.Connected) (hPD : D.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected)
    (hCore : (D.cornerDiagram hPD).RotationRigid)
    (hEnds : ∀ (t : ℤ) (ht : 0 < t),
      ((D.cornerDiagram hPD).extendTop t ht).schur =
        ((D.cornerDiagram hPD).extendBottom t ht).schur →
        (D.cornerDiagram hPD).Symmetric)
    (he : D.schur = E.schur) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  let hPE := D.positiveCorner_of_cornerPolynomial_eq E hD hE hPD
    (D.cornerPolynomial_eq_of_schur_eq E hD hE he)
  have hCE : (E.cornerDiagram hPE).Connected :=
    D.connected_corner_of_corner_eq E hD hE hPD hCD he
  have hcEq : (D.cornerDiagram hPD).schur = (E.cornerDiagram hPE).schur :=
    D.cornerPolynomial_eq_of_schur_eq E hD hE he
  rcases (rotationRigid_iff_same_order _).mp hCore _ hCE hcEq.symm with htr | hrot
  · exact D.connected_border_aligned_rigidity E hD hE hPD hPE hCD hCE htr hEnds he
  · have hEr := E.rotate_connected hE
    have hEqr : D.schur = E.rotate.schur := he.trans (E.rotate_schur.symm)
    have hCr : (E.rotate.cornerDiagram (E.rotate_positiveCorner hPE)).Connected := by
      apply connected_of_schur_irreducible _ (by omega)
      rw [← (D.corner_translation_of_rotation E hPD hPE hrot).schur_eq]
      exact (D.cornerDiagram hPD).schur_irreducible hCD
    rcases D.connected_border_aligned_rigidity E.rotate hD hEr hPD
        (E.rotate_positiveCorner hPE) hCD hCr
        (D.corner_translation_of_rotation E hPD hPE hrot) hEnds hEqr with hh | hh
    · exact Or.inr ((D.translation_rotate_iff_rotation E).mp hh)
    · exact Or.inl ((D.rotation_rotate_iff_translation E).mp hh)

/-- The minimal connected-border hypothesis also covers arbitrary mate row counts. -/
theorem connected_border_endpoint_isolation (D : BetaDiagram (n + 3))
    (hD : D.Connected) (hPD : D.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected)
    (hCore : (D.cornerDiagram hPD).RotationRigid)
    (hEnds : ∀ (t : ℤ) (ht : 0 < t),
      ((D.cornerDiagram hPD).extendTop t ht).schur =
        ((D.cornerDiagram hPD).extendBottom t ht).schur →
        (D.cornerDiagram hPD).Symmetric) : D.RotationRigid := by
  apply (rotationRigid_iff_same_order D).mpr
  intro E hE he
  exact D.connected_border_endpoint_isolation_same_order E hD hE hPD hCD hCore hEnds he.symm

/-- The connected-child clause of `lem:border`; the mate has no board-pattern premise. -/
theorem connected_border_rigidity_same_order (D E : BetaDiagram (n + 3))
    (hD : D.Connected) (hE : E.Connected) (hPD : D.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected)
    (hCore : (D.cornerDiagram hPD).RotationRigid)
    (hEndpoint : ∀ (t : ℤ) (ht : 0 < t),
      ((D.cornerDiagram hPD).extendTop t ht).RotationRigid)
    (he : D.schur = E.schur) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  have hEnds : ∀ (t : ℤ) (ht : 0 < t),
      ((D.cornerDiagram hPD).extendTop t ht).schur =
        ((D.cornerDiagram hPD).extendBottom t ht).schur →
        (D.cornerDiagram hPD).Symmetric := by
    intro t ht hext
    rcases (rotationRigid_iff_same_order _).mp (hEndpoint t ht) _
        ((D.cornerDiagram hPD).extendBottom_connected hCD t ht) hext.symm with hh | hh
    · exact False.elim ((D.cornerDiagram hPD).extendTop_not_translation_extendBottom t ht hh)
    · exact (D.cornerDiagram hPD).symmetric_of_extendTop_rotation_extendBottom t ht hh
  exact D.connected_border_endpoint_isolation_same_order E hD hE hPD hCD hCore hEnds he

/-- Connected bordering is rigid against mates of arbitrary row count. -/
theorem connected_border_rigidity (D : BetaDiagram (n + 3))
    (hD : D.Connected) (hPD : D.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected)
    (hCore : (D.cornerDiagram hPD).RotationRigid)
    (hEndpoint : ∀ (t : ℤ) (ht : 0 < t),
      ((D.cornerDiagram hPD).extendTop t ht).RotationRigid) : D.RotationRigid := by
  apply (rotationRigid_iff_same_order D).mpr
  intro E hE he
  exact D.connected_border_rigidity_same_order E hD hE hPD hCD hCore hEndpoint he.symm

end SkewJacobiNegative.BetaDiagram
