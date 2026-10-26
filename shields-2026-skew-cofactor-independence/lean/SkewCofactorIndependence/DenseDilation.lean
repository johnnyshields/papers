/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.NonsymmetricCofactors
import SkewCofactorIndependence.KernelNullity

/-!
# Dilation of dense nonsymmetric cores

The automatic dense-class specialization in `thm:dilation` and
`cor:nullity-increment` of `shields-2026-skew-cofactor-independence.tex`.
Cofactor independence is produced by the cofactor theorem, not retained as an
additional hypothesis.  Density also supplies connectedness and zero-freeness.
-/

namespace SkewCofactorIndependence.BetaDiagram

variable {n : ℕ}

/-- The actual direct sum for every dense nonsymmetric core, in its original coordinates. -/
theorem dense_nonsymmetric_dilation_kernel (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hd : D.Dense) (hs : ¬ D.Symmetric) :
    (D.dilate t).unitKernel = D.inheritedKernel t ⊔ D.relativeArithmeticOffGrid t ∧
      Disjoint (D.inheritedKernel t) (D.relativeArithmeticOffGrid t) :=
  D.dilation_kernel_general t hn (hd.connected (by omega)) hd.zeroFree
    (D.nonsymmetric_cofactor_independent hd hs)

/-- Exact nullity increase without an undischarged cofactor-independence premise. -/
theorem dense_nonsymmetric_dilation_nullity (D : BetaDiagram (n + 1)) (t : ℕ+)
    (hn : 1 ≤ n) (hd : D.Dense) (hs : ¬ D.Symmetric) :
    Module.finrank ℚ (D.dilate t).unitKernel = Module.finrank ℚ D.unitKernel +
      Module.finrank ℚ (offGridResidueSpace (t : ℕ)
        D.normalizeBetas.endpointModulus D.normalizeBetas.span) :=
  D.dilation_nullity_add_general t hn (hd.connected (by omega)) hd.zeroFree
    (D.nonsymmetric_cofactor_independent hd hs)

/-- Modulus one gives the floor formula on the dense nonsymmetric class. -/
theorem dense_nonsymmetric_dilation_nullity_modulus_one (D : BetaDiagram (n + 1))
    (t : ℕ+) (hn : 1 ≤ n) (hd : D.Dense) (hs : ¬ D.Symmetric)
    (hg : D.normalizeBetas.endpointModulus = 1) :
    Module.finrank ℚ (D.dilate t).unitKernel - Module.finrank ℚ D.unitKernel =
      ((t : ℕ) - 1) / 2 :=
  D.dilation_nullity_modulus_one_general t hn (hd.connected (by omega)) hd.zeroFree
    (D.nonsymmetric_cofactor_independent hd hs) hg

end SkewCofactorIndependence.BetaDiagram
