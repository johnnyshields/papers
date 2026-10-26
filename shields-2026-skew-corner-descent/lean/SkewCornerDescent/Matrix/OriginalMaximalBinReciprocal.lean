/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SignedReciprocalNonvanishing
import SkewCornerDescent.Matrix.OriginalRationalClassTransfer

/-!
# Nonvanishing signed reciprocal factor on the actual closure chart

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). The actual
virtual central responses share a produced nonzero scale times the original
transcendental closure coordinate minus each rational label. A nonzero signed
degree produces the required nonvanishing reciprocal factor. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

noncomputable local instance maximalBinReciprocalRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The reciprocal factor of the actual virtual classes cannot vanish when their
signed degree is nonzero. Neither a nonvanishing sum nor a scale is assumed. -/
theorem originalVirtual_signed_reciprocal_ne_zero {n m : ℕ}
    (P : Profile n) (Q : Profile m) (w : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (s : Finset ℚ) (e : ℚ → ℤ) (hdegree : (∑ α ∈ s, e α) ≠ 0) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    (∑ α ∈ s, (e α : OtherField c.top) /
      c.originalVirtualCentralResponse P Q middle α) ≠ 0 := by
  classical
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by
      rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by
    rw [originalHorizontalClosure_profile_selected_count P Q w hQ]
    omega
  have hmaxQ := c.originalHorizontalClosure_profile_component_span P Q w hQ hmax
  have hf := c.originalSchur_residue_ne_zero P hB hmax
  have hβ := c.originalSchur_residue_ne_zero Q hBQ hmaxQ
  have hS := c.originalHessenberg_residue_ne_zero Q hBQ hmaxQ middle
  let u := c.residueMap Q.schur / c.residueMap P.schur ^ 2
  let A := c.regularResidue (c.originalHessenbergResponse Q middle middle) *
    c.residueMap P.schur ^ 2 / c.residueMap Q.schur
  have hA : A ≠ 0 := div_ne_zero (mul_ne_zero hS (pow_ne_zero 2 hf)) hβ
  have hu := c.originalHorizontalClosure_residue_transcendental P Q w hQ hB hmax
  have hweights : ∃ α ∈ s, e α ≠ 0 := by
    by_contra hnot
    push Not at hnot
    exact hdegree (Finset.sum_eq_zero (fun α hα => hnot α hα))
  have hL := transcendental_signed_reciprocal_sum_ne_zero u hu s e hweights
  have hfactor (α : ℚ) : c.originalVirtualCentralResponse P Q middle α =
      A * (u - (α : OtherField c.top)) := by
    unfold originalVirtualCentralResponse
    dsimp only [A, u]
    field_simp [hf, hβ]
  have hscale : (∑ α ∈ s, (e α : OtherField c.top) /
      c.originalVirtualCentralResponse P Q middle α) =
        A⁻¹ * ∑ α ∈ s, (e α : OtherField c.top) / (u - (α : OtherField c.top)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [hfactor]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  dsimp only
  rw [hscale]
  exact mul_ne_zero (inv_ne_zero hA) hL

/-- The complete virtual determinant residues have a nonvanishing signed
reciprocal inventory. The actual source square is the common produced scale. -/
theorem originalVirtualResidue_signed_reciprocal_ne_zero {n m : ℕ}
    (P : Profile n) (Q : Profile m) (w : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (s : Finset ℚ) (e : ℚ → ℤ) (hdegree : (∑ α ∈ s, e α) ≠ 0) :
    (∑ α ∈ s, (e α : OtherField c.top) /
      (c.residueMap Q.schur - (α : OtherField c.top) * c.residueMap P.schur ^ 2)) ≠ 0 := by
  classical
  have hf := c.originalSchur_residue_ne_zero P hB hmax
  let u := c.residueMap Q.schur / c.residueMap P.schur ^ 2
  have hu := c.originalHorizontalClosure_residue_transcendental P Q w hQ hB hmax
  have hweights : ∃ α ∈ s, e α ≠ 0 := by
    by_contra hnot
    push Not at hnot
    exact hdegree (Finset.sum_eq_zero fun α hα => hnot α hα)
  have hL := transcendental_signed_reciprocal_sum_ne_zero u hu s e hweights
  have hfactor (α : ℚ) :
      c.residueMap Q.schur - (α : OtherField c.top) * c.residueMap P.schur ^ 2 =
        c.residueMap P.schur ^ 2 * (u - (α : OtherField c.top)) := by
    dsimp only [u]
    field_simp [hf]
  have hscale : (∑ α ∈ s, (e α : OtherField c.top) /
      (c.residueMap Q.schur - (α : OtherField c.top) * c.residueMap P.schur ^ 2)) =
      (c.residueMap P.schur ^ 2)⁻¹ *
        ∑ α ∈ s, (e α : OtherField c.top) / (u - (α : OtherField c.top)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [hfactor]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hscale]
  exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hf)) hL

end SkewCornerDescent.Matrix.SelectedCoordinate
