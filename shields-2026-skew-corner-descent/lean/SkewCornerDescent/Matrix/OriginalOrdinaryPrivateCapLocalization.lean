/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivateUnitCapLocalization

/-!
# The actual ordinary private-cap contraction and its vertical unit

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The literal ordinary edge determines the unit's existence. The original
coordinate interval supplies its membership, so neither a cut unit nor its
absence is carried as an unexplained input. Complete nonrow inverses remain.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

private theorem ordinary_unit_self_contraction {F : Type*} [CommRing F]
    (A T : LaurentPolynomial F) (z k : ℤ)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0)
    (hA0 : A.coeff 0 = 1) (hT0 : T.coeff 0 = 1) :
    A.coeff (z - k) * T.coeff (k - z) = if z = k then 1 else 0 := by
  by_cases h : z = k
  · subst z
    simp only [sub_self, hA0, hT0, mul_one, ite_true]
  · rw [ite_eq_right h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [hA _ (sub_neg.mpr hlt), zero_mul]
    · rw [hT _ (sub_neg.mpr hgt), mul_zero]

/-- The complete actual lower-side projection is its clipped cap plus exactly
one unit at the cut in the vertical ordinary case. Both presence and absence
are produced from the actual private cells. -/
theorem originalOrdinaryPrivate_lower_cap_projection {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = k) (hp : content prev = k - 1)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hkprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hb : k < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))
    (hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) < k)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : z ≤ k)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0)
    (hA0 : A.coeff 0 = 1) (hT0 : T.coeff 0 = 1) :
    c.originalIntervalInverseProjection P (some b) (some d) A T z =
      c.originalFilteredCapInverseProjection P 0 k true d A T z +
        if z = k ∧ cur.2 = prev.2 then 1 else 0 := by
  classical
  have hiff := originalRemaining_private_unit_iff_vertical (hD := hD) P k cur prev
    hcur hprev hc hp hk hkprev
  by_cases hcol : cur.2 = prev.2
  · obtain ⟨j, hj⟩ := hiff.mpr hcol
    obtain ⟨u, _, hu⟩ := originalInterval_of_remaining_unit P b d k j hj hb hd
    have h := c.originalInterval_private_lower_cap_with_unit P b d k hk hkprev hb
      u hu A T z hz hA hT
    rw [ordinary_unit_self_contraction A T z k hA hT hA0 hT0] at h
    simpa only [hcol, and_true] using h
  · have hno (i : OriginalResponseInterval (hD := hD) P (some b) (some d)) :
        ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k) := by
      intro hi
      exact hcol (hiff.mp ⟨i.1.1, hi⟩)
    have h := c.originalInterval_private_lower_cap_without_unit P b d k hk hkprev hb
      hno A T z hz hA hT
    simpa only [hcol, and_false, ite_false, add_zero] using h

/-- The corresponding complete upper-side projection has the same produced
vertical unit correction, with no diagonal approximation of the retained cap. -/
theorem originalOrdinaryPrivate_upper_cap_projection {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = k) (hp : content prev = k - 1)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hkprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hb : k < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))
    (hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) < k)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : k ≤ z)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0)
    (hA0 : A.coeff 0 = 1) (hT0 : T.coeff 0 = 1) :
    c.originalIntervalInverseProjection P (some b) (some d) A T z =
      c.originalFilteredCapInverseProjection P k (P.xi 0) false b A T z +
        if z = k ∧ cur.2 = prev.2 then 1 else 0 := by
  classical
  have hiff := originalRemaining_private_unit_iff_vertical (hD := hD) P k cur prev
    hcur hprev hc hp hk hkprev
  by_cases hcol : cur.2 = prev.2
  · obtain ⟨j, hj⟩ := hiff.mpr hcol
    obtain ⟨u, _, hu⟩ := originalInterval_of_remaining_unit P b d k j hj hb hd
    have h := c.originalInterval_private_upper_cap_with_unit P b d k hk hkprev hd
      u hu A T z hz hA hT
    rw [ordinary_unit_self_contraction A T z k hA hT hA0 hT0] at h
    simpa only [hcol, and_true] using h
  · have hno (i : OriginalResponseInterval (hD := hD) P (some b) (some d)) :
        ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k) := by
      intro hi
      exact hcol (hiff.mp ⟨i.1.1, hi⟩)
    have h := c.originalInterval_private_upper_cap_without_unit P b d k hk hkprev hd
      hno A T z hz hA hT
    simpa only [hcol, and_false, ite_false, add_zero] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
