/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureQuotient
import SkewCornerDescent.Matrix.OriginalNormalLog

/-!
# Complete normal-series closure quotient

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:original-transfer`).
The complete removed factor cancels before any coefficient extraction. Both actual
response determinant series retain their full inverse dependence. The integer orientation
sign remains explicit. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual diagonal occurrence produces nonvanishing of the original Schur residue. -/
theorem originalSchur_residue_ne_zero {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    c.residueMap P.schur ≠ 0 := by
  classical
  obtain ⟨ε, hε, he⟩ := c.originalHessenberg_residue_signed_factorization P
  rw [he]
  apply mul_ne_zero
  · apply mul_ne_zero
    · rcases hε with h | h <;> simp [h]
    · exact (c.originalRemoved_residue_lower_scalar P hmax).2
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact c.originalHessenberg_residue_ne_zero P hB hmax i

/-- The complete regular-ring relation cancels the removed two-copy factor without dividing
by a possibly vanishing response determinant. -/
theorem originalHorizontalClosure_regular_cross {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      algebraMap Lambda c.RegularRing Q.schur * (c.originalHessenbergResponse P).det ^ 2 =
        (ε : c.RegularRing) * (algebraMap Lambda c.RegularRing P.schur) ^ 2 *
          (c.originalHessenbergResponse Q).det := by
  obtain ⟨εP, hεP, hP⟩ := c.originalHessenberg_local_signed_factorization P
  obtain ⟨εQ, hεQ, hQ'⟩ := c.originalHessenberg_local_signed_factorization Q
  have hs : (εP : c.RegularRing) ^ 2 = 1 := by
    rcases hεP with h | h <;> simp [h]
  refine ⟨εQ, hεQ, ?_⟩
  rw [hP, hQ', originalHorizontalClosure_removed_square P Q v hQ, map_pow,
    mul_pow, mul_pow, hs, one_mul]
  ring

/-- Actual residue nonvanishing supplies the source unit, so the full original normal quotient
is the quotient of full response determinant series. No residue-only replacement is made. -/
theorem originalHorizontalClosure_normal_quotient {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      c.normalPolynomialSeries Q.schur * (c.normalPolynomialSeries P.schur)⁻¹ ^ 2 =
        (ε : PowerSeries (OtherField c.top)) *
          c.normalSeries (c.originalHessenbergResponse Q).det *
            (c.normalSeries (c.originalHessenbergResponse P).det)⁻¹ ^ 2 := by
  obtain ⟨ε, hε, he⟩ := c.originalHorizontalClosure_regular_cross P Q v hQ
  have hn := congrArg c.normalSeries he
  simp only [map_mul, map_pow, map_intCast, c.normalSeries_polynomial] at hn
  have hp := PowerSeries.mul_inv_cancel (c.normalPolynomialSeries P.schur)
    (by simpa only [c.normalPolynomialSeries_constant] using
      c.originalSchur_residue_ne_zero P hB hmax)
  have ht := PowerSeries.mul_inv_cancel (c.normalSeries (c.originalHessenbergResponse P).det)
    (c.originalHessenberg_normalSeries_constant_ne_zero P hB hmax)
  have hp2 : (c.normalPolynomialSeries P.schur) ^ 2 *
      (c.normalPolynomialSeries P.schur)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, hp, one_pow]
  have ht2 : (c.normalSeries (c.originalHessenbergResponse P).det) ^ 2 *
      (c.normalSeries (c.originalHessenbergResponse P).det)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, ht, one_pow]
  refine ⟨ε, hε, ?_⟩
  calc
    _ = (c.normalPolynomialSeries Q.schur *
        (c.normalSeries (c.originalHessenbergResponse P).det) ^ 2) *
        (c.normalPolynomialSeries P.schur)⁻¹ ^ 2 *
        (c.normalSeries (c.originalHessenbergResponse P).det)⁻¹ ^ 2 := by
      calc
        _ = (c.normalPolynomialSeries Q.schur *
            (c.normalPolynomialSeries P.schur)⁻¹ ^ 2) *
            ((c.normalSeries (c.originalHessenbergResponse P).det) ^ 2 *
              (c.normalSeries (c.originalHessenbergResponse P).det)⁻¹ ^ 2) := by
          rw [ht2, mul_one]
        _ = _ := by ring
    _ = _ := by rw [hn]; calc
      _ = (ε : PowerSeries (OtherField c.top)) *
          c.normalSeries (c.originalHessenbergResponse Q).det *
          ((c.normalPolynomialSeries P.schur) ^ 2 *
            (c.normalPolynomialSeries P.schur)⁻¹ ^ 2) *
          (c.normalSeries (c.originalHessenbergResponse P).det)⁻¹ ^ 2 := by ring
      _ = _ := by rw [hp2, mul_one]

/-- Unit normalization removes the produced orientation sign from the complete normal germ.
The response quotient still contains the full source inverse, not merely its residue. -/
theorem originalHorizontalClosure_normalized_quotient {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let f := c.normalPolynomialSeries Q.schur * (c.normalPolynomialSeries P.schur)⁻¹ ^ 2
    let t := c.normalSeries (c.originalHessenbergResponse Q).det *
      (c.normalSeries (c.originalHessenbergResponse P).det)⁻¹ ^ 2
    PowerSeries.C (PowerSeries.constantCoeff f)⁻¹ * f =
      PowerSeries.C (PowerSeries.constantCoeff t)⁻¹ * t := by
  obtain ⟨ε, hε, he⟩ := c.originalHorizontalClosure_normal_quotient P Q v hQ hB hmax
  dsimp only
  rw [he]
  rcases hε with h | h <;>
    simp [h, map_mul, mul_assoc]

end SkewCornerDescent.Matrix.SelectedCoordinate
