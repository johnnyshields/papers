/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCoreProductJets
import SkewCornerDescent.Matrix.OriginalWindowSelectedTranslation
import SkewGluing.ProfileInvariant

/-!
# Literal selected component transport fixes proper profiles

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Complete translated selected components have the same canonical dependent
profile, so both proper-core polynomials agree without Schur-equivalence being
used as a substitute for literal equality. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- A complete translated nonempty component has the same normalized profile,
including its dependent row index. -/
theorem interiorBlockProfile_sigma_of_translate {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b : Fin n) (d : Fin m) (hb : P.zeta b.castSucc < P.xi b.succ)
    (hd : Q.zeta d.castSucc < Q.xi d.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b) = interiorBlockCells Q d) :
    (⟨interiorBlockLength P b, interiorBlockProfile P b hb⟩ : Σ k, Profile k) =
      ⟨interiorBlockLength Q d, interiorBlockProfile Q d hd⟩ := by
  have hp : ∃ u, interiorBlockCells P b = translate u (interiorBlockProfile P b hb).cells := by
    exact ⟨_, interiorSliceCells_eq_translate P _ _ _ (interiorBlock_slice_same P b)
      (interiorBlock_first_nonempty P b hb)⟩
  have hq : ∃ w, interiorBlockCells Q d = translate w (interiorBlockProfile Q d hd).cells := by
    exact ⟨_, interiorSliceCells_eq_translate Q _ _ _ (interiorBlock_slice_same Q d)
      (interiorBlock_first_nonempty Q d hd)⟩
  obtain ⟨u, hu⟩ := hp
  obtain ⟨w, hw⟩ := hq
  rw [hu, hw, translate_translate] at he
  exact Profile.presentation_sigma_unique he

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Canonical dependent profile equality transports both complete proper-core
polynomials, including every inverse entry and the empty proper core. -/
theorem selected_core_polynomials_eq_of_sigma {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur)
    (he : (⟨n, P⟩ : Σ k, Profile k) = ⟨m, Q⟩) :
    c.selectedCoreLeftPolynomial P hP = c.selectedCoreLeftPolynomial Q hQ ∧
      c.selectedCoreRightPolynomial P hP = c.selectedCoreRightPolynomial Q hQ := by
  cases he
  exact ⟨rfl, rfl⟩

/-- Complete literal selected-block translation supplies both proper-core
polynomial equalities from the actual source profiles. -/
theorem original_selected_core_polynomials_of_translate {n m : ℕ} (P : Profile n)
    (Q : Profile m) (b : OriginalSelectedBlocks (hD := hD) P)
    (d : OriginalSelectedBlocks (hD := hD) Q) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q d.val.val) :
    c.selectedCoreLeftPolynomial
        (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
        (originalSelectedProfile_schur P b).symm =
      c.selectedCoreLeftPolynomial
        (interiorBlockProfile Q d.val.val (originalBlockSelected_nonempty Q d.val d.property))
        (originalSelectedProfile_schur Q d).symm ∧
    c.selectedCoreRightPolynomial
        (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
        (originalSelectedProfile_schur P b).symm =
      c.selectedCoreRightPolynomial
        (interiorBlockProfile Q d.val.val (originalBlockSelected_nonempty Q d.val d.property))
        (originalSelectedProfile_schur Q d).symm := by
  exact c.selected_core_polynomials_eq_of_sigma _ _ _ _
    (interiorBlockProfile_sigma_of_translate P Q b.val.val d.val.val
      (originalBlockSelected_nonempty P b.val b.property)
      (originalBlockSelected_nonempty Q d.val d.property) v he)

end SelectedCoordinate
end SkewCornerDescent.Matrix
