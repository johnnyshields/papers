/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ActualResponseExposure
import SkewCornerDescent.ExposureTopology

/-!
# Nonempty open exposure chambers for actual responses

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Complete original response representatives produce open nonempty chambers on an exposed
root section. The selected response is zero throughout the section; every other response
has the prescribed strict sign and a nonvanishing denominator.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

/-- The free-coordinate chamber of an exposed member of a represented actual family. -/
noncomputable def actualExposureChamber {ι : Type*} (N K : ℕ+) (top : ι → ℕ+)
    (p q : ι → OtherPolynomial N) (a : ι) (positive : Bool) : Set (ℕ → ℝ) :=
  {x | MvPolynomial.eval x (realResiduePolynomial N (q a)) ≠ 0 ∧
    ∀ i : {i : ι // i ≠ a},
      let y := Function.update x (K : ℕ)
        (-(MvPolynomial.eval x (realResiduePolynomial N (p a)) /
          MvPolynomial.eval x (realResiduePolynomial N (q a))))
      MvPolynomial.eval y (realResiduePolynomial N (q i.val)) ≠ 0 ∧
        responseSign positive (rationalTriangularResponse (top i.val : ℕ)
          (realResiduePolynomial N (p i.val)) (realResiduePolynomial N (q i.val)) y)}

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual original matrices supply nonempty open chambers of either exposed sign. -/
theorem originalResponses_open_exposure {ι : Type*} [Finite ι]
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
    (positive : Bool) :
    ∃ (p q : ι → OtherPolynomial c.top) (a : ι), top a = K ∧
      (∀ i, c.regularResidue (c.originalLocalResponse (P i) (b i) (d i)) =
        residueGenerator c.top ⟨top i, ne_of_gt (htop i)⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (p i) /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) (q i)) ∧
      IsOpen (actualExposureChamber c.top K top p q a positive) ∧
      (actualExposureChamber c.top K top p q a positive).Nonempty ∧
      ∀ x, rationalTriangularResponse (K : ℕ) (realResiduePolynomial c.top (p a))
        (realResiduePolynomial c.top (q a))
        (Function.update x (K : ℕ)
          (-(MvPolynomial.eval x (realResiduePolynomial c.top (p a)) /
            MvPolynomial.eval x (realResiduePolynomial c.top (q a))))) = 0 := by
  classical
  obtain ⟨p, q, hp, hq, _, he, y, a, ha, hreg, hz, hs⟩ :=
    c.originalResponses_exposure n P b d top htop hindices hmax K hanchor hdistinct positive
  refine ⟨p, q, a, ha, he, ?_, ?_, ?_⟩
  · exact rational_anchor_chamber_open (ι := {i : ι // i ≠ a}) (K : ℕ)
      (realResiduePolynomial c.top (p a)) (realResiduePolynomial c.top (q a))
      (fun i => (top i.val : ℕ)) (fun i => realResiduePolynomial c.top (p i.val))
      (fun i => realResiduePolynomial c.top (q i.val)) positive
  · exact rational_anchor_chamber_nonempty (ι := {i : ι // i ≠ a}) (K : ℕ)
      (realResiduePolynomial c.top (p a)) (realResiduePolynomial c.top (q a))
      (fun i => (top i.val : ℕ)) (fun i => realResiduePolynomial c.top (p i.val))
      (fun i => realResiduePolynomial c.top (q i.val)) positive y (hreg a) hz
      (fun i => hreg i.val) (fun i => hs i.val i.property)
  · intro x
    apply rational_anchor_response_zero (α := Unit) (K : ℕ)
      (fun _ => realResiduePolynomial c.top (p a))
      (fun _ => realResiduePolynomial c.top (q a))
      (fun _ j hj => by simpa only [ha] using hp a j hj)
      (fun _ j hj => lt_of_lt_of_le (hq a j hj) (by
        exact_mod_cast (ha ▸ htop a).le)) () x

end SelectedCoordinate
end SkewCornerDescent.Matrix
