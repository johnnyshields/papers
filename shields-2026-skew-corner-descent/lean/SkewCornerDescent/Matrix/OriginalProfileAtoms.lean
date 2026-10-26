/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitEmptySeparation

/-!
# Source-produced atoms of complete nonselected endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Every actual nonselected row or column, including an empty pivot, has the
protected top of its own complete component. The full leading coefficient,
nonvanishing, and lower-field remainder are produced from genuine original
inverses. This asserts nonvanishing of full endpoint coefficients, not all
internal inverse entries. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

private theorem interval_unit_position {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (k : OriginalResponseInterval (hD := hD) P b d)
    (hs : ¬ originalBlockSelected (hD := hD) P k.1.1.1) :
    ∃ i : Fin (interiorBlockLength P k.1.1.1.val + 1),
      originalIntervalUnitIndex P b d k.1.1.1 hs ⟨k.2, k.1.2⟩ i = k := by
  obtain ⟨q, hq⟩ := originalIntervalUnitPrefixIndex_surjective_through
    P b d k.1.1.1 hs ⟨k.2, k.1.2⟩ k le_rfl
  rcases q with q | q
  · have he := congrArg (fun z : OriginalResponseInterval (hD := hD) P b d => z.1.1.1) hq
    change q.val.1.1.1 = k.1.1.1 at he
    exact False.elim ((ne_of_lt q.property) he)
  · exact ⟨q, hq⟩

/-- Every actual nonselected incoming row has its original least-column
protected top, including empty pivots. The leading coefficient, its
nonvanishing, and the full lower-field remainder are all source-produced. -/
theorem original_interval_incoming_atom {n : ℕ} (P : Profile n)
    (a : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (k : OriginalResponseInterval (hD := hD) P (some a) d)
    (hs : ¬ originalBlockSelected (hD := hD) P k.1.1.1)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    let row := fun i : OriginalResponseInterval (hD := hD) P (some a) d =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P (some a) d =>
      originalResponseCols P i.1.1
    ∃ J : ℕ+, (J : ℤ) = x - originalComponentTau P k.1.1.1 ∧ ∃ hJ : c.top < J,
      ∃ α ∈ residueLowerField c.top J, α ≠ 0 ∧ ∃ R ∈ residueLowerField c.top J,
        (vertexOutgoing c.residueMap col x * (vertexBetaMatrix c.residueMap row col)⁻¹) () k =
          residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * α + R := by
  let u := k.1.1.1
  let hu := And.intro k.2 k.1.2
  by_cases hempty : P.xi u.val.succ = P.zeta u.val.castSucc
  · obtain ⟨J, hJe, hJ, R, hR, hvalue⟩ := c.original_empty_interval_incoming_top P a d k hempty
    have hTau : originalComponentTau P u = P.xi u.val.succ := by
      rw [originalComponentTau, (interior_empty_block_extremes P u.val hempty).2, ← hempty]
    refine ⟨J, ?_, hJ, 1, (residueLowerField c.top J).one_mem,
      (one_ne_zero : (1 : OtherField c.top) ≠ 0), R, hR, ?_⟩
    · change (J : ℤ) =
        P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) - originalComponentTau P u
      rw [hTau]
      exact hJe
    · simpa only [mul_one] using hvalue
  · have hne : P.zeta u.val.castSucc < P.xi u.val.succ := by
      have h := P.zeta_le_xi_succ u.val
      omega
    obtain ⟨i, hik⟩ := interval_unit_position P (some a) d k hs
    obtain ⟨J, hJe, hJ, α, hα, hα0, R, hR, hvalue⟩ :=
      c.original_interval_incoming_protected_top P a d u hs hne hu hmax i
    rw [hik] at hvalue
    exact ⟨J, hJe, hJ, α, hα, hα0, R, hR, hvalue⟩

/-- Every actual outgoing unit column has the top given by the component's
actual greatest original row. This also includes literal empty pivots. -/
theorem original_interval_outgoing_atom {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (k : OriginalResponseInterval (hD := hD) P b (some d))
    (hs : ¬ originalBlockSelected (hD := hD) P k.1.1.1)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
    let row := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
      originalResponseCols P i.1.1
    ∃ J : ℕ+, (J : ℤ) = P.xi (interiorBlockFirst P k.1.1.1.val).succ - y ∧
      ∃ hJ : c.top < J, ∃ α ∈ residueLowerField c.top J, α ≠ 0 ∧
      ∃ R ∈ residueLowerField c.top J,
        ((vertexBetaMatrix c.residueMap row col)⁻¹ * vertexIncoming c.residueMap row y) k () =
          α * residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  let u := k.1.1.1
  let hu := And.intro k.2 k.1.2
  by_cases hempty : P.xi u.val.succ = P.zeta u.val.castSucc
  · obtain ⟨J, hJe, hJ, R, hR, hvalue⟩ := c.original_empty_interval_outgoing_top P b d k hempty
    refine ⟨J, ?_, hJ, 1, (residueLowerField c.top J).one_mem,
      (one_ne_zero : (1 : OtherField c.top) ≠ 0), R, hR, ?_⟩
    · rw [(interior_empty_block_extremes P u.val hempty).1]
      exact hJe
    · simpa only [one_mul] using hvalue
  · have hne : P.zeta u.val.castSucc < P.xi u.val.succ := by
      have h := P.zeta_le_xi_succ u.val
      omega
    obtain ⟨i, hik⟩ := interval_unit_position P b (some d) k hs
    obtain ⟨J, hJe, hJ, α, hα, hα0, R, hR, hvalue⟩ :=
      c.original_interval_outgoing_protected_top P b d u hs hne hu hmax i
    rw [hik] at hvalue
    have hGreatest : (interiorBlockProfile P u.val hne).xi 0 + originalComponentTau P u =
        P.xi (interiorBlockFirst P u.val).succ := by
      have h := (original_unit_component_beta P u hs hne 0).1
      rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first] at h
      exact h.symm
    refine ⟨J, ?_, hJ, α, hα, hα0, R, hR, hvalue⟩
    rwa [hGreatest] at hJe

/-- Every nonselected row has a nonzero coefficient in the complete actual
incoming profile, including every full positive-span block and empty pivot. -/
theorem original_nonselected_left_profile_ne_zero {n : ℕ} (P : Profile n)
    (a : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (k : OriginalResponseInterval (hD := hD) P (some a) d)
    (hs : ¬ originalBlockSelected (hD := hD) P k.1.1.1)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    (c.originalResidueLeftEndpointPolynomial P (some a) d).coeff
      (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
        originalResponseRows P k.1.1).toNat ≠ 0 := by
  obtain ⟨J, _, hJ, α, hα, hα0, R, hR, hvalue⟩ :=
    c.original_interval_incoming_atom P a d k hs hmax
  have hv0 := c.residue_protected_affine_ne_zero J hJ α R hα hα0 hR
  have hp := c.original_left_profile_coeff_at_row P (some a) d k
  dsimp only at hp hvalue
  rw [hp, hvalue]
  exact neg_ne_zero.mpr hv0

/-- The same produced nonvanishing holds for every complete outgoing unit
coefficient, not for arbitrary internal inverse entries. -/
theorem original_nonselected_right_profile_ne_zero {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (k : OriginalResponseInterval (hD := hD) P b (some d))
    (hs : ¬ originalBlockSelected (hD := hD) P k.1.1.1)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    (c.originalResidueRightEndpointPolynomial P b (some d)).coeff
      (originalResponseCols P k.1.1 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))).toNat ≠ 0 := by
  obtain ⟨J, _, hJ, α, hα, hα0, R, hR, hvalue⟩ :=
    c.original_interval_outgoing_atom P b d k hs hmax
  have hv0 := c.residue_protected_affine_ne_zero J hJ α R hα hα0 hR
  have hp := c.original_right_profile_coeff_at_col P b (some d) k
  dsimp only at hp hvalue
  rw [hp, hvalue]
  simpa only [mul_comm α] using neg_ne_zero.mpr hv0

end SkewCornerDescent.Matrix.SelectedCoordinate
