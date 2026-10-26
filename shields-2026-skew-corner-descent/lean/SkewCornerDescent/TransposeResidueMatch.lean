/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.ResidueTransposeEquiv

/-!
# Actual rational residue matching under whole-diagram transpose

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The produced full residue-field map fixes rational coefficients and transports
the same source, window, and closure functions in the standing residue match.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)
variable (d : SelectedCoordinate (transpose D) (isConnectedSkew_transpose hD))

/-- Rational polynomial evaluation commutes with the produced actual residue-field map. -/
theorem residueTranspose_aeval [Algebra ℚ (OtherField c.top)] [Algebra ℚ (OtherField d.top)]
    (x : OtherField c.top) (p : Polynomial ℚ) :
    c.residueTranspose d (Polynomial.aeval x p) =
      Polynomial.aeval (c.residueTranspose d x) p := by
  have h := Polynomial.map_aeval_eq_aeval_map (φ := RingHom.id ℚ)
    (ψ := c.residueTranspose d) (RingHom.ext_rat _ _) p x
  simpa only [Polynomial.map_id] using h

/-- The actual full skew Schur residue is transported with every geometric component. -/
theorem residueTranspose_cellSchur (P : Diagram) (hs : IsSkew P) :
    c.residueTranspose d (c.residueMap (cellSchur P hs)) =
      d.residueMap (cellSchur (transpose P) (isSkew_transpose hs)) := by
  rw [c.residueTranspose_residueMap d, schurInvolution_skew_cellSchur]

/-- The standing rational match transports for the complete actual source,
window, and closure; the rational numerator and denominator are unchanged. -/
theorem rational_residue_match_transpose
    (P W Q : Diagram) (hP : IsSkew P) (hW : IsSkew W) (hQ : IsSkew Q)
    (a b : ℕ) (p₀ p₁ : Polynomial ℚ)
    (hdep : c.residueMap (cellSchur P hP) ^ a / c.residueMap (cellSchur W hW) ^ b =
      Polynomial.aeval (c.residueMap (cellSchur Q hQ) /
        c.residueMap (cellSchur P hP) ^ 2) p₀ /
      Polynomial.aeval (c.residueMap (cellSchur Q hQ) /
        c.residueMap (cellSchur P hP) ^ 2) p₁) :
    d.residueMap (cellSchur (transpose P) (isSkew_transpose hP)) ^ a /
      d.residueMap (cellSchur (transpose W) (isSkew_transpose hW)) ^ b =
      Polynomial.aeval (d.residueMap (cellSchur (transpose Q) (isSkew_transpose hQ)) /
        d.residueMap (cellSchur (transpose P) (isSkew_transpose hP)) ^ 2) p₀ /
      Polynomial.aeval (d.residueMap (cellSchur (transpose Q) (isSkew_transpose hQ)) /
        d.residueMap (cellSchur (transpose P) (isSkew_transpose hP)) ^ 2) p₁ := by
  have h := congrArg (c.residueTranspose d) hdep
  simpa only [map_div₀, map_pow, c.residueTranspose_aeval d,
    c.residueTranspose_cellSchur d] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
