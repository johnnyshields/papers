/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularPlanePolynomial
import SkewCornerDescent.PlanePolynomialAffine
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# Irreducibility of genuine triangular plane numerators

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Splitting at the closure generator gives
a monic polynomial. Its evaluated coefficient polynomial is an irreducible affine
pullback, so monicity descends irreducibility to the original polynomial algebra.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

variable {σ k E : Type*} [LinearOrder σ] [Field k] [Field E] [Algebra k E]

/-- Monicity descends affine irreducibility back to the original-coordinate polynomial. -/
theorem triangularPlanePolynomial_irreducible
    (w : MvPolynomial σ k →ₐ[k] E) {K : σ} {p : Polynomial k} (hp : p.Monic)
    (hirr : Irreducible (p.map (algebraMap k E))) {A F : MvPolynomial σ k}
    (hA : ∀ i ∈ A.vars, i < K) (hF : ∀ i ∈ F.vars, i < K) (hF0 : w F ≠ 0) :
    Irreducible (triangularPlanePolynomial K p A F) := by
  classical
  let e : MvPolynomial σ k ≃ₐ[k] Polynomial (MvPolynomial {i // i ≠ K} k) :=
    (renameEquiv k (Equiv.optionSubtypeNe K).symm).trans (optionEquivLeft k _)
  let g : MvPolynomial {i // i ≠ K} k →ₐ[k] E :=
    w.comp (e.symm.toAlgHom.comp Polynomial.CAlgHom)
  have hconst (r : MvPolynomial σ k) (hr : ∀ i ∈ r.vars, i < K) :
      g ((e r).coeff 0) = w r := by
    change w (e.symm (Polynomial.C ((e r).coeff 0))) = w r
    rw [← triangularCorrection_split_constant hr, AlgEquiv.symm_apply_apply]
  apply (MulEquiv.irreducible_iff e).mp
  apply Polynomial.Monic.irreducible_of_irreducible_map g.toRingHom _
    (triangularPlanePolynomial_split_monic hp hA hF)
  have he : (e (triangularPlanePolynomial K p A F)).map g.toRingHom =
      clearedPlanePolynomial p (w A) (w F) := by
    rw [triangularPlanePolynomial_split e K p A F ((e A).coeff 0) ((e F).coeff 0)
      (by simp [e, optionEquivLeft_apply]) (triangularCorrection_split_constant hA)
      (triangularCorrection_split_constant hF), clearedPlanePolynomial_map g hp,
      hconst A hA, hconst F hF]
  change Irreducible ((e (triangularPlanePolynomial K p A F)).map g.toRingHom)
  rw [he]
  exact clearedPlanePolynomial_irreducible _ _ hF0 hirr

end SkewCornerDescent
