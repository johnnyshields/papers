/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.RealResiduePolynomials

/-!
# Real charts of finite actual retained responses

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

The chart representatives are supplied by complete original-matrix elimination, not by
assuming triangularity of newly defined responses. Their real numerators and denominators
preserve the literal original top indices and every nonzero cross-difference.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A finite actual response family has simultaneous faithful lower-denominator representatives. -/
theorem originalResponses_real_representatives {ι : Type*}
    (n : ι → ℕ) (P : ∀ i, Profile (n i))
    (b d : ∀ i, Option (OriginalSelectedBlocks (hD := hD) (P i)))
    (K : ι → ℕ+) (hNK : ∀ i, c.top < K i)
    (hK : ∀ i, (P i).xi (originalRowSplitEquiv (hD := hD) (P i) (.inl (b i))) -
      (P i).zeta (originalColSplitEquiv (hD := hD) (P i) (.inl (d i))) = (K i : ℤ))
    (hmax : ∀ i C, C ∈ edgeComponents (diagramInterior (P i).cells) →
      span C ≤ (c.top : ℕ)) :
    ∃ p q : ι → OtherPolynomial c.top,
      (∀ i, ∀ j ∈ (realResiduePolynomial c.top (p i)).vars, j < (K i : ℕ)) ∧
      (∀ i, ∀ j ∈ (realResiduePolynomial c.top (q i)).vars, j < (c.top : ℕ)) ∧
      (∀ i, q i ≠ 0) ∧ (∀ i, realResiduePolynomial c.top (q i) ≠ 0) ∧
      ∀ i, c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) =
        residueGenerator c.top ⟨K i, ne_of_gt (hNK i)⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (p i) /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) (q i) := by
  classical
  choose p hp q hq hq0 he using fun i =>
    c.originalLocalResponse_residue_representatives (P i) (b i) (d i) (K i)
      (hNK i) (hK i) (hmax i)
  exact ⟨p, q, fun i => realResiduePolynomial_vars_lt c.top (K i) (hp i),
    fun i => realResiduePolynomial_vars_lt c.top c.top (hq i), hq0,
    fun i => realResiduePolynomial_ne_zero c.top (hq0 i), he⟩

/-- Distinct actual responses at the same top retain distinct real anchor corrections. -/
theorem originalResponses_real_cross_difference (K : ℕ+) (hNK : c.top < K)
    {x y : OtherField c.top} (p q r s : OtherPolynomial c.top)
    (hq : q ≠ 0) (hs : s ≠ 0)
    (hx : x = residueGenerator c.top ⟨K, ne_of_gt hNK⟩ +
      algebraMap (OtherPolynomial c.top) (OtherField c.top) p /
        algebraMap (OtherPolynomial c.top) (OtherField c.top) q)
    (hy : y = residueGenerator c.top ⟨K, ne_of_gt hNK⟩ +
      algebraMap (OtherPolynomial c.top) (OtherField c.top) r /
        algebraMap (OtherPolynomial c.top) (OtherField c.top) s)
    (hne : x ≠ y) :
    realResiduePolynomial c.top p * realResiduePolynomial c.top s -
      realResiduePolynomial c.top r * realResiduePolynomial c.top q ≠ 0 := by
  apply real_cross_difference_ne_zero c.top p q r s hq hs
  intro he
  apply hne
  rw [hx, hy, he]

end SkewCornerDescent.Matrix.SelectedCoordinate
