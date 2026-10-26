/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ActualExposureExtremes
import SkewCornerDescent.Matrix.TrueCapExposureTops

/-!
# Two-chamber exposure for actual original response families

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

One collection of rational representatives works in both sign chambers. True caps
whose literal tops lie below the closure top have positive product at every root.
At each point an extreme anchor exposes itself and signs all other represented classes.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both real exposure chambers use the same actual residue representatives. -/
theorem originalResponses_two_exposure_chambers {ι : Type*} [Finite ι]
    (n : ι → ℕ) (P : ∀ i, Profile (n i))
    (b d : ∀ i, Option (OriginalSelectedBlocks (hD := hD) (P i)))
    (top : ι → ℕ+) (htop : ∀ i, c.top < top i)
    (hindices : ∀ i, (P i).xi (originalRowSplitEquiv (hD := hD) (P i) (.inl (b i))) -
      (P i).zeta (originalColSplitEquiv (hD := hD) (P i) (.inl (d i))) = (top i : ℤ))
    (hmax : ∀ i C, C ∈ edgeComponents (diagramInterior (P i).cells) →
      span C ≤ (c.top : ℕ))
    (K : ℕ+) (hanchor : ∃ i, top i = K)
    (hdistinct : ∀ i j, top i = K → top j = K → i ≠ j →
      c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) ≠
        c.regularResidue (c.originalLocalResponse (P j) (b j) (d j)))
    (left right : ι) (hleft : top left < K) (hright : top right < K) :
    ∃ p q : ι → OtherPolynomial c.top,
      (∀ i, c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) =
        residueGenerator c.top ⟨top i, ne_of_gt (htop i)⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (p i) /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) (q i)) ∧
      ∀ positive : Bool,
        IsOpen (simultaneousActualChamber c.top K top p q positive) ∧
        (simultaneousActualChamber c.top K top p q positive).Nonempty ∧
        ∀ x ∈ simultaneousActualChamber c.top K top p q positive,
          (∀ a : {i : ι // top i = K},
            let y := anchorAssignment (K : ℕ)
              (rationalAnchorRoot (fun a => realResiduePolynomial c.top (p a.val))
                (fun a => realResiduePolynomial c.top (q a.val))) a x
            0 < rationalTriangularResponse (top left : ℕ)
              (realResiduePolynomial c.top (p left)) (realResiduePolynomial c.top (q left)) y *
              rationalTriangularResponse (top right : ℕ)
                (realResiduePolynomial c.top (p right))
                (realResiduePolynomial c.top (q right)) y) ∧
          ∃ a : {i : ι // top i = K},
            let y := anchorAssignment (K : ℕ)
              (rationalAnchorRoot (fun a => realResiduePolynomial c.top (p a.val))
                (fun a => realResiduePolynomial c.top (q a.val))) a x
            rationalTriangularResponse (K : ℕ) (realResiduePolynomial c.top (p a.val))
              (realResiduePolynomial c.top (q a.val)) y = 0 ∧
            (∀ i, MvPolynomial.eval y (realResiduePolynomial c.top (q i)) ≠ 0) ∧
            ∀ i, i ≠ a.val → responseSign positive
              (rationalTriangularResponse (top i : ℕ) (realResiduePolynomial c.top (p i))
                (realResiduePolynomial c.top (q i)) y) := by
  obtain ⟨p, q, hp, hq, he, hchamber⟩ :=
    c.originalResponses_simultaneous_chambers n P b d top htop hindices hmax
      K hanchor hdistinct
  obtain ⟨i0, hi0⟩ := hanchor
  have hNK : c.top ≤ K := (hi0 ▸ htop i0).le
  refine ⟨p, q, he, ?_⟩
  intro positive
  refine ⟨(hchamber positive).1, (hchamber positive).2, ?_⟩
  intro x hx
  refine ⟨?_, simultaneousActualChamber_exposed_extreme c.top K hNK top p q
    hp hq ⟨i0, hi0⟩ positive x hx⟩
  intro a
  exact (simultaneousActualChamber_cap_product_pos c.top K top p q positive left right
    (ne_of_lt hleft) (ne_of_lt hright) x hx a).2.2

end SkewCornerDescent.Matrix.SelectedCoordinate
