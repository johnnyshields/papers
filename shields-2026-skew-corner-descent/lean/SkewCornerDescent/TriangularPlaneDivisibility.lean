/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularPlanePolynomial
import SkewCornerDescent.PlanePolynomialFactors

/-!
# Protected-coordinate factor exclusion

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). The canonical closure split prevents
numerator factors from cancelling against the cap denominator or a coprime plane factor.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

variable {k σ E : Type*} [Field k] [LinearOrder σ] [Field E] [Algebra k E]

/-- Split the selected coordinate and evaluate only the remaining coefficient variables. -/
noncomputable def protectedCoordinateEval (K : σ) (w : MvPolynomial σ k →ₐ[k] E) :
    MvPolynomial σ k →ₐ[k] Polynomial E :=
  let e := (renameEquiv k (Equiv.optionSubtypeNe K).symm).trans (optionEquivLeft k _)
  let g := w.comp (e.symm.toAlgHom.comp Polynomial.CAlgHom)
  (Polynomial.mapAlgHom g).comp e.toAlgHom

/-- A strictly lower correction specializes to its actual field value as a constant. -/
theorem protectedCoordinateEval_lower (K : σ) (w : MvPolynomial σ k →ₐ[k] E)
    {r : MvPolynomial σ k} (hr : ∀ i ∈ r.vars, i < K) :
    protectedCoordinateEval K w r = Polynomial.C (w r) := by
  classical
  let e := (renameEquiv k (Equiv.optionSubtypeNe K).symm).trans (optionEquivLeft k _)
  have he : e r = Polynomial.C ((e r).coeff 0) := triangularCorrection_split_constant hr
  change (e r).map (w.comp (e.symm.toAlgHom.comp Polynomial.CAlgHom)).toRingHom = _
  rw [he, Polynomial.map_C]
  congr 1
  change w (e.symm (Polynomial.C ((e r).coeff 0))) = w r
  rw [← he, AlgEquiv.symm_apply_apply]

/-- The closure specialization retains the full cleared numerator for every polynomial. -/
theorem protectedCoordinateEval_plane (K : σ) (w : MvPolynomial σ k →ₐ[k] E)
    (p : Polynomial k) {A F : MvPolynomial σ k}
    (hA : ∀ i ∈ A.vars, i < K) (hF : ∀ i ∈ F.vars, i < K) :
    protectedCoordinateEval K w (triangularPlanePolynomial K p A F) =
      clearedPlanePolynomial p (w A) (w F) := by
  classical
  let e := (renameEquiv k (Equiv.optionSubtypeNe K).symm).trans (optionEquivLeft k _)
  let g := w.comp (e.symm.toAlgHom.comp Polynomial.CAlgHom)
  have hg (r : MvPolynomial σ k) (hr : ∀ i ∈ r.vars, i < K) :
      g ((e r).coeff 0) = w r := by
    change w (e.symm (Polynomial.C ((e r).coeff 0))) = w r
    rw [← triangularCorrection_split_constant hr, AlgEquiv.symm_apply_apply]
  change (e (triangularPlanePolynomial K p A F)).map g.toRingHom = _
  rw [triangularPlanePolynomial_split e K p A F ((e A).coeff 0) ((e F).coeff 0)
    (by simp [e, optionEquivLeft_apply]) (triangularCorrection_split_constant hA)
    (triangularCorrection_split_constant hF), clearedPlanePolynomial_map_all g,
    hg A hA, hg F hF]

/-- A positive-degree plane numerator cannot divide a nonzero lower cap expression. -/
theorem triangularPlanePolynomial_not_dvd_lower (K : σ)
    (w : MvPolynomial σ k →ₐ[k] E) {p : Polynomial k} (hp : p.Monic)
    (hdeg : 0 < p.natDegree) {A F r : MvPolynomial σ k}
    (hA : ∀ i ∈ A.vars, i < K) (hF : ∀ i ∈ F.vars, i < K)
    (hr : ∀ i ∈ r.vars, i < K) (hr0 : w r ≠ 0) :
    ¬ triangularPlanePolynomial K p A F ∣ r := by
  intro hd
  have hm := _root_.map_dvd (protectedCoordinateEval K w) hd
  rw [protectedCoordinateEval_plane K w p hA hF, protectedCoordinateEval_lower K w hr] at hm
  have hu := isUnit_of_dvd_unit hm (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hr0))
  have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [clearedPlanePolynomial_natDegree hp] at hd0
  omega

/-- Coprime plane factors cannot cancel after denominator clearing in the original variables. -/
theorem triangularPlanePolynomial_not_dvd_coprime (K : σ)
    (w : MvPolynomial σ k →ₐ[k] E) {p q : Polynomial k} (hp : p.Monic)
    (hdeg : 0 < p.natDegree) (hpq : IsCoprime p q) {A F : MvPolynomial σ k}
    (hA : ∀ i ∈ A.vars, i < K) (hF : ∀ i ∈ F.vars, i < K) (hF0 : w F ≠ 0) :
    ¬ triangularPlanePolynomial K p A F ∣ triangularPlanePolynomial K q A F := by
  intro hd
  have hm := _root_.map_dvd (protectedCoordinateEval K w) hd
  rw [protectedCoordinateEval_plane K w p hA hF,
    protectedCoordinateEval_plane K w q hA hF] at hm
  have hu := (clearedPlanePolynomial_isCoprime hpq (w A) (w F) hF0).isUnit_of_dvd hm
  have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [clearedPlanePolynomial_natDegree hp] at hd0
  omega

omit [LinearOrder σ] in
/-- Every rational polynomial divisor produces a divisor of the original cleared numerator. -/
theorem triangularPlanePolynomial_dvd (K : σ) {p q : Polynomial k}
    (hpq : p ∣ q) (A F : MvPolynomial σ k) :
    triangularPlanePolynomial K p A F ∣ triangularPlanePolynomial K q A F :=
  _root_.map_dvd (Polynomial.evalRingHom (MvPolynomial.X K))
    (clearedPlanePolynomial_dvd hpq A F)

omit [LinearOrder σ] in
/-- Evaluation of an arbitrary numerator commutes with original-coordinate denominator clearing. -/
theorem triangularPlanePolynomial_eval_all (w : MvPolynomial σ k →ₐ[k] E)
    (K : σ) (p : Polynomial k) (A F : MvPolynomial σ k) :
    w (triangularPlanePolynomial K p A F) =
      (clearedPlanePolynomial p (w A) (w F)).eval (w (X K)) := by
  change w.toRingHom ((clearedPlanePolynomial p A F).eval (X K)) = _
  rw [← Polynomial.eval₂_at_apply w.toRingHom,
    Polynomial.eval₂_eq_eval_map, clearedPlanePolynomial_map_all w]
  rfl

end SkewCornerDescent
