/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.PlanePolynomial
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Affine recovery of denominator-cleared plane factors

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Undoing the cap scaling and closure
correction recovers the constant polynomial times a nonzero scalar. An affine
polynomial automorphism therefore preserves its irreducibility.

Sorry-free.
-/

namespace SkewCornerDescent

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- Undoing the actual affine substitution recovers the complete constant plane factor. -/
theorem clearedPlanePolynomial_comp_affine (p : Polynomial k) (A F : E) :
    (clearedPlanePolynomial p A F).comp (Polynomial.C F * Polynomial.X + Polynomial.C (-A)) =
      Polynomial.C (F ^ p.natDegree) * p.map (algebraMap k E) := by
  rw [clearedPlanePolynomial, Polynomial.comp_assoc]
  have hinner : (Polynomial.X + Polynomial.C A).comp
      (Polynomial.C F * Polynomial.X + Polynomial.C (-A)) = Polynomial.C F * Polynomial.X := by
    simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, map_neg]
    ring
  rw [hinner]
  have h := Polynomial.scaleRoots_eval₂_mul
    (p := p.map (algebraMap k E)) Polynomial.C Polynomial.X F
  simpa only [Polynomial.comp, Polynomial.eval₂_C_X, Polynomial.natDegree_map,
    ← map_pow] using h

/-- A nonzero cap denominator and a faithful constant factor yield an irreducible pullback. -/
theorem clearedPlanePolynomial_irreducible {p : Polynomial k} (A F : E) (hF : F ≠ 0)
    (hp : Irreducible (p.map (algebraMap k E))) :
    Irreducible (clearedPlanePolynomial p A F) := by
  let : Invertible F := invertibleOfNonzero hF
  let e := Polynomial.algEquivCMulXAddC F (-A)
  have he : e (clearedPlanePolynomial p A F) =
      Polynomial.C (F ^ p.natDegree) * p.map (algebraMap k E) := by
    change (clearedPlanePolynomial p A F).comp
      (Polynomial.C F * Polynomial.X + Polynomial.C (-A)) = _
    exact clearedPlanePolynomial_comp_affine p A F
  have hu : IsUnit (Polynomial.C (F ^ p.natDegree)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hF))
  have hi : Irreducible (e (clearedPlanePolynomial p A F)) := by
    rw [he]
    exact (associated_unit_mul_left _ _ hu).symm.irreducible hp
  exact (MulEquiv.irreducible_iff e).mp hi

end SkewCornerDescent
