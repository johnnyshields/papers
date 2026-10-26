/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.RationalReflection
import SkewCornerDescent.RegularRingTranspose
import SkewCornerDescent.Matrix.OriginalClosureNormalQuotient

/-!
# Actual closure-coordinate reflection and transposed rational matching

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The actual parent residue supplies the nonzero square denominator. Complementary
empty closures produce the coordinate reflection, and full residue-field transport
then supplies the standing rational match on the transposed horizontal reference.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

noncomputable local instance closureReflectionRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete vertical reference is the complement of the horizontal one
in the actual residue field. The parent square denominator is produced nonzero. -/
theorem originalClosures_normalized_complement {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    c.residueMap (cellSchur (originalVerticalClosure P) (originalVerticalClosure_connected P).1) /
        c.residueMap P.schur ^ 2 =
      1 - c.residueMap (cellSchur (originalHorizontalClosure P)
        (originalHorizontalClosure_connected P).1) / c.residueMap P.schur ^ 2 := by
  have hp := c.originalSchur_residue_ne_zero P hB hmax
  have hs := congrArg c.residueMap (empty_closure_schur_complement P)
  rw [map_add, map_pow] at hs
  have he : c.residueMap (cellSchur (originalVerticalClosure P)
      (originalVerticalClosure_connected P).1) = c.residueMap P.schur ^ 2 -
      c.residueMap (cellSchur (originalHorizontalClosure P)
        (originalHorizontalClosure_connected P).1) := by
    linear_combination hs
  rw [he, sub_div, div_self (pow_ne_zero 2 hp)]

variable (d : SelectedCoordinate (transpose D) (isConnectedSkew_transpose hD))

/-- Full residue transport follows every actual transposed profile presentation. -/
theorem residueTranspose_profile_schur {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells) :
    c.residueTranspose d (c.residueMap P.schur) = d.residueMap T.schur := by
  rw [← cellSchur_cells P, c.residueTranspose_cellSchur d]
  have he := cellSchur_congr ha (isSkew_transpose P.isSkew_cells)
    (isSkew_translate a T.isSkew_cells)
  rw [he, cellSchur_translate T.cells T.isSkew_cells a, cellSchur_cells]

/-- The complete original vertical closure becomes the actual horizontal
closure of the normalized transposed source in the same produced residue field. -/
theorem residueTranspose_vertical_closure {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells) :
    c.residueTranspose d (c.residueMap
      (cellSchur (originalVerticalClosure P) (originalVerticalClosure_connected P).1)) =
      d.residueMap (cellSchur (originalHorizontalClosure T)
        (originalHorizontalClosure_connected T).1) := by
  rw [c.residueTranspose_cellSchur d]
  have he := vertical_closure_transpose_profile P T a ha
  have ht := isConnectedSkew_transpose (originalVerticalClosure_connected P)
  rw [cellSchur_congr he (originalHorizontalClosure_connected T).1
      (isSkew_translate _ ht.1), cellSchur_translate _ ht.1]

/-- Whole-diagram transposition supplies the standing rational match on the
actual horizontal closure, with a produced coprime reflected polynomial pair. -/
theorem original_rational_match_transpose_horizontal {n k m s t : ℕ}
    (P : Profile n) (W : Profile k) (T : Profile m) (S : Profile s) (Q : Profile t)
    (v z h : ℤ × ℤ) (hT : transpose P.cells = translate v T.cells)
    (hS : transpose W.cells = translate z S.cells)
    (hQ : originalHorizontalClosure T = translate h Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (a b : ℕ) (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap (cellSchur (originalHorizontalClosure P)
        (originalHorizontalClosure_connected P).1) / c.residueMap P.schur ^ 2) p₀ /
      Polynomial.aeval (c.residueMap (cellSchur (originalHorizontalClosure P)
        (originalHorizontalClosure_connected P).1) / c.residueMap P.schur ^ 2) p₁) :
    IsCoprime (rationalReflection p₀) (rationalReflection p₁) ∧
      d.residueMap T.schur ^ a / d.residueMap S.schur ^ b =
        Polynomial.aeval (d.residueMap Q.schur / d.residueMap T.schur ^ 2)
            (rationalReflection p₀) /
          Polynomial.aeval (d.residueMap Q.schur / d.residueMap T.schur ^ 2)
            (rationalReflection p₁) := by
  refine ⟨rationalReflection_isCoprime hpq, ?_⟩
  have hv := c.originalClosures_normalized_complement P hB hmax
  have hdepV : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap (cellSchur (originalVerticalClosure P)
        (originalVerticalClosure_connected P).1) / c.residueMap P.schur ^ 2)
          (rationalReflection p₀) /
      Polynomial.aeval (c.residueMap (cellSchur (originalVerticalClosure P)
        (originalVerticalClosure_connected P).1) / c.residueMap P.schur ^ 2)
          (rationalReflection p₁) := by
    rw [hv, rationalReflection_fraction]
    exact hdep
  have hm := congrArg (c.residueTranspose d) hdepV
  simp only [map_div₀, map_pow, c.residueTranspose_aeval d] at hm
  rw [c.residueTranspose_profile_schur d P T v hT,
    c.residueTranspose_profile_schur d W S z hS,
    c.residueTranspose_vertical_closure d P T v hT] at hm
  have he := cellSchur_eq_profile (originalHorizontalClosure_connected T) Q h hQ
  rw [he] at hm
  exact hm

end SkewCornerDescent.Matrix.SelectedCoordinate
