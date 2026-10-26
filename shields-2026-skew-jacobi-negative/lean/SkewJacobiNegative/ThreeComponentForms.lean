/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.DenseThreeComponentPlacements

/-!
# Three-component source forms

The explicit source-form output of `lem:three-component-forms`, starting from
an actual maximal-cofactor product rather than a preselected context.
-/
namespace SkewJacobiNegative.BetaDiagram

/-- Every dense-four-plus-two-singletons source has the actual end or middle
lists, with core motion and both singleton orders recovered internally. -/
theorem dense_three_component_source_forms (D : BetaDiagram 7)
    (hD : D.Connected) (hZ : D.ZeroFree) (Q : BetaDiagram 4) (hQ : Q.Dense)
    (ell m : ℤ) (hℓ : 0 < ell) (hm : 0 < m)
    (hcof : D.cornerPolynomial = complete ell * complete m * Q.schur) :
    ∃ (R : BetaDiagram 4) (P : ThreeComponentParameters),
      R.Normalized ∧ Q.MotionEquivalent R ∧
        ((ell = P.ell ∧ m = P.m) ∨ (ell = P.m ∧ m = P.ell)) ∧
        (D.TranslationEquivalent (R.threeEndContext P) ∨
          D.TranslationEquivalent (R.threeMiddleContext P) ∨
          D.rotate.TranslationEquivalent (R.threeEndContext P)) := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let C := D.cornerDiagram hP
  let K := C.componentDecomposition
  have hQC := hQ.connected (by omega)
  have hprod : complete ell * complete m * Q.schur = C.schur := by
    rw [cornerDiagram_schur, hcof]
  have hrel := C.component_matching_of_product K
    ([⟨1, singletonDiagram ell hℓ⟩, ⟨1, singletonDiagram m hm⟩, ⟨4, Q⟩] :
      List (Σ a : ℕ, BetaDiagram a))
    (by
      intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl
      · exact singletonDiagram_connected ell hℓ
      · exact singletonDiagram_connected m hm
      · exact hQC)
    (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      singletonDiagram_schur, mul_one, mul_assoc] using hprod)
  have recover (F : BetaDiagram 7) (hFC : F.Connected)
      (hFcof : F.cornerPolynomial = complete ell * complete m * Q.schur)
      (R : BetaDiagram 4) (P : ThreeComponentParameters) (b : Bool)
      (htr : F.TranslationEquivalent (if b then R.threeMiddleContext P else R.threeEndContext P)) :
      Q.MotionEquivalent R ∧
        ((ell = P.ell ∧ m = P.m) ∨ (ell = P.m ∧ m = P.ell)) := by
    let S := if b then R.threeMiddleContext P else R.threeEndContext P
    have hSC : S.Connected := by
      cases b
      · exact R.threeEndContext_connected P
      · exact R.threeMiddleContext_connected P
    have hc := F.cornerPolynomial_eq_of_schur_eq S hFC hSC htr.schur_eq
    have hSc : S.cornerPolynomial = complete P.ell * complete P.m * R.schur := by
      cases b <;> simp [S]
    rw [hFcof, hSc] at hc
    obtain ⟨hRC, hfun, hpair⟩ := three_product_core_recovery Q R hQC
      ell m P.ell P.m hℓ hm P.ell_pos P.m_pos hc
    exact ⟨Q.rotationRigid_of_nonnegative hQC hQ.nonnegative 4 R hRC hfun.symm, hpair⟩
  rcases C.three_cuts_of_factor_inventory K Q ell m hℓ hm hrel with hcuts | hcuts | hcuts
  · obtain ⟨R, P, hRN, htr⟩ := D.three_end_parent_of_cuts hP hcuts.1 hcuts.2
    obtain ⟨hQR, hpair⟩ := recover D hD hcof R P false htr
    exact ⟨R, P, hRN, hQR, hpair, Or.inl htr⟩
  · obtain ⟨R, P, hRN, htr⟩ := D.three_middle_parent_of_cuts hP hcuts.1 hcuts.2
    obtain ⟨hQR, hpair⟩ := recover D hD hcof R P true htr
    exact ⟨R, P, hRN, hQR, hpair, Or.inr (Or.inl htr)⟩
  · have hcut₁ : D.rotate.row 2 < D.rotate.col 0 := by
      have h : D.row 6 < D.col 4 := hcuts.2
      change -D.col 4 < -D.row 6
      omega
    have hcut₂ : D.rotate.row 3 < D.rotate.col 1 := by
      have h : D.row 5 < D.col 3 := hcuts.1
      change -D.col 3 < -D.row 5
      omega
    have hRC := D.rotate_connected hD
    have hRP := D.rotate_positiveCorner hP
    obtain ⟨R, P, hRN, htr⟩ := D.rotate.three_end_parent_of_cuts hRP hcut₁ hcut₂
    have hc : D.rotate.cornerPolynomial = complete ell * complete m * Q.schur := by
      have he := D.cornerPolynomial_eq_of_schur_eq D.rotate hD hRC D.rotate_schur.symm
      rw [hcof] at he
      exact he.symm
    obtain ⟨hQR, hpair⟩ := recover D.rotate hRC hc R P false htr
    exact ⟨R, P, hRN, hQR, hpair, Or.inr (Or.inr htr)⟩

end SkewJacobiNegative.BetaDiagram
