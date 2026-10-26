/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIntervalIncomingLocality
import SkewCornerDescent.Matrix.OriginalIntervalOutgoingLocality
import SkewCornerDescent.Matrix.OriginalUnitProtectedPositions

/-!
# Source-produced protected tops of actual retained unit-component coefficients

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Actual selected endpoints supply the high generator. The full retained prefix
supplies its inverse and all earlier couplings. Every component row has its
actual common nonzero affine top, not an assumed protected-coefficient model.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every complete unit-component row in a selected-start interval has the genuine
least-column protected top, with both nonvanishing and lower-field remainder produced. -/
theorem original_interval_incoming_protected_top {n : ℕ} (P : Profile n)
    (a : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hu : originalResponseLowerCut P (some a) < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : Fin (interiorBlockLength P u.val + 1)) :
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    let row := fun i : OriginalResponseInterval (hD := hD) P (some a) d =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P (some a) d =>
      originalResponseCols P i.1.1
    ∃ J : ℕ+, (J : ℤ) = x - originalComponentTau P u ∧ ∃ hJ : c.top < J,
      ∃ α ∈ residueLowerField c.top J, α ≠ 0 ∧ ∃ R ∈ residueLowerField c.top J,
        (vertexOutgoing c.residueMap col x * (vertexBetaMatrix c.residueMap row col)⁻¹)
          () (originalIntervalUnitIndex P (some a) d u hs hu j) =
          residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * α + R := by
  classical
  let Q := interiorBlockProfile P u.val hne
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let τ := originalComponentTau P u
  have hab : interiorBlock P a.val.val < interiorBlock P u.val := by
    have h := hu.1
    change (interiorBlock P a.val.val : ℤ) - 1 < (interiorBlock P u.val : ℤ) at h
    have hneBlock : a.val ≠ u := by
      intro he
      exact hs (he ▸ a.property)
    have hlabels : (interiorBlock P a.val.val : ℤ) ≠ (interiorBlock P u.val : ℤ) := by
      exact_mod_cast fun he => hneBlock ((originalBlocks_label_strictMono P).injective he)
    have hlt : (interiorBlock P a.val.val : ℤ) < (interiorBlock P u.val : ℤ) := by omega
    exact_mod_cast hlt
  have hhigh := c.original_unit_incoming_positions_high P a u hab hs hne (Fin.last _)
  change (c.top : ℤ) < x - (Q.zeta (Fin.last _) + τ) at hhigh
  rw [Q.zeta_last, zero_add] at hhigh
  let J := higherIndexFromInteger c.top (x - τ) hhigh
  have hJ : c.top < J.val := J.property
  have hJe : (J.val : ℤ) = x - τ := higherIndexFromInteger_coe _ _ _
  have hx : (J.val : ℤ) + τ = x := by omega
  let row := fun i : OriginalIntervalUnitPrefix (hD := hD) P (some a) d u =>
    originalResponseRows P i.1.1.1
  let col := fun i : OriginalIntervalUnitPrefix (hD := hD) P (some a) d u =>
    originalResponseCols P i.1.1.1
  let := c.originalIntervalUnitPrefixInverse P (some a) d u
  have hrow (i) : row i < (J.val : ℤ) + τ := by
    rw [hx]
    exact originalResponse_row_lt P (some a) i.val.1.1 i.val.2
  have hsep (i k) : Q.xi i + τ < col k :=
    original_interval_unit_prefix_separation P (some a) d u hs hne i k
  have hcol (i) : τ < col i := by
    have h := hsep 0 i
    have hQ := Q.topVar.pos
    have he := Q.topVar_coe
    omega
  have hunit := original_unit_component_schur_ne P u hs hne
  have hspan := c.original_unit_component_top_le P u hs hne hmax
  obtain ⟨hα0, hα, R, hR, hvalue⟩ := c.ordered_component_original_incoming_top Q
    hunit hspan row col τ J.val hJ hrow hcol hsep j
  refine ⟨J.val, hJe, hJ, _, hα, hα0, R, hR, ?_⟩
  rw [c.original_interval_incoming_prefix_value P (some a) d u hs hne hu x j]
  rw [Matrix.invOf_eq_nonsing_inv] at hvalue
  simpa only [hx] using hvalue

/-- The dual selected-end interval produces the actual greatest-row protected
top of every full component column, including its complete later-block correction. -/
theorem original_interval_outgoing_protected_top {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P (some d))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : Fin (interiorBlockLength P u.val + 1)) :
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
    let Q := interiorBlockProfile P u.val hne
    let row := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
      originalResponseCols P i.1.1
    ∃ J : ℕ+, (J : ℤ) = Q.xi 0 + originalComponentTau P u - y ∧
      ∃ hJ : c.top < J,
      ∃ α ∈ residueLowerField c.top J, α ≠ 0 ∧ ∃ R ∈ residueLowerField c.top J,
        ((vertexBetaMatrix c.residueMap row col)⁻¹ * vertexIncoming c.residueMap row y)
          (originalIntervalUnitIndex P b (some d) u hs hu j) () =
          α * residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  classical
  let Q := interiorBlockProfile P u.val hne
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
  let τ := originalComponentTau P u
  have hud : interiorBlock P u.val < interiorBlock P d.val.val := by
    have h := hu.2
    change (interiorBlock P u.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1 at h
    have hneBlock : u ≠ d.val := by
      intro he
      exact hs (he.symm ▸ d.property)
    have hlabels : (interiorBlock P u.val : ℤ) ≠ (interiorBlock P d.val.val : ℤ) := by
      exact_mod_cast fun he => hneBlock ((originalBlocks_label_strictMono P).injective he)
    have hlt : (interiorBlock P u.val : ℤ) < (interiorBlock P d.val.val : ℤ) := by omega
    exact_mod_cast hlt
  have hhigh := c.original_unit_outgoing_positions_high P u d hud hs hne 0
  change (c.top : ℤ) < Q.xi 0 + τ - y at hhigh
  let J := higherIndexFromInteger c.top (Q.xi 0 + τ - y) hhigh
  have hJ : c.top < J.val := J.property
  have hJe : (J.val : ℤ) = Q.xi 0 + τ - y := higherIndexFromInteger_coe _ _ _
  have hy : Q.xi 0 + τ - (J.val : ℤ) = y := by omega
  let row := fun i : OriginalIntervalUnitSuffix (hD := hD) P b (some d) u =>
    originalResponseRows P i.1.1.1
  let col := fun i : OriginalIntervalUnitSuffix (hD := hD) P b (some d) u =>
    originalResponseCols P i.1.1.1
  let := c.originalIntervalUnitSuffixInverse P b (some d) u
  have hsep (i k) : row i < Q.zeta k + τ :=
    original_interval_unit_suffix_separation P b (some d) u hs hne k i
  have hrow (i) : row i < Q.xi 0 + τ := by
    have h := hsep i 0
    have hp := Q.r_pos 0
    have he := Q.xi_sub_zeta 0
    change 0 < (Q.r 0 : ℕ) at hp
    change Q.xi 0 - Q.zeta 0 = (Q.r 0 : ℤ) at he
    omega
  have hcol (i) : Q.xi 0 + τ - (J.val : ℤ) < col i := by
    rw [hy]
    exact originalResponse_col_gt P (some d) i.val.1.1 i.val.1.2
  have hunit := original_unit_component_schur_ne P u hs hne
  have hspan := c.original_unit_component_top_le P u hs hne hmax
  obtain ⟨hα0, hα, R, hR, hvalue⟩ := c.ordered_component_original_outgoing_top Q
    hunit hspan row col τ J.val hJ hrow hcol hsep j
  refine ⟨J.val, hJe, hJ, _, hα, hα0, R, hR, ?_⟩
  rw [c.original_interval_outgoing_suffix_value P b (some d) u hs hne hu y j]
  rw [Matrix.invOf_eq_nonsing_inv] at hvalue
  simpa only [hy] using hvalue

end SkewCornerDescent.Matrix.SelectedCoordinate
