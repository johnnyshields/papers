/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# Denominator-cleared rational plane polynomials

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Clearing the cap denominator of a monic
plane polynomial preserves its leading coefficient in the closure coordinate.

Sorry-free.
-/

namespace SkewCornerDescent

open Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- The polynomial numerator of `p((X + A)/F)`, without inverting a cap factor. -/
noncomputable def clearedPlanePolynomial (p : Polynomial k) (A F : R) : Polynomial R :=
  ((p.map (algebraMap k R)).scaleRoots F).comp (X + C A)

/-- Cap denominator clearing introduces no coefficient-ring prime factor. -/
theorem clearedPlanePolynomial_monic [Nontrivial R] {p : Polynomial k}
    (hp : p.Monic) (A F : R) : (clearedPlanePolynomial p A F).Monic :=
  ((monic_scaleRoots_iff F).mpr (hp.map (algebraMap k R))).comp
    (monic_X_add_C A) (by rw [natDegree_X_add_C]; exact one_ne_zero)

/-- The closure-coordinate degree is the rational plane degree. -/
theorem clearedPlanePolynomial_natDegree [IsDomain R] {p : Polynomial k}
    (hp : p.Monic) (A F : R) : (clearedPlanePolynomial p A F).natDegree = p.natDegree := by
  rw [clearedPlanePolynomial, natDegree_comp, natDegree_X_add_C, mul_one,
    natDegree_scaleRoots, natDegree_map_of_leadingCoeff_ne_zero]
  rw [hp.leadingCoeff, map_one]
  exact one_ne_zero

/-- A nonzero cap denominator gives the exact numerator identity in the original field. -/
theorem clearedPlanePolynomial_eval {E : Type*} [Field E] [Algebra k E]
    (p : Polynomial k) (A F z : E) (hF : F ≠ 0) :
    (clearedPlanePolynomial p A F).eval z =
      F ^ p.natDegree * Polynomial.aeval ((z + A) / F) p := by
  rw [clearedPlanePolynomial, eval_comp, eval_add, eval_X, eval_C]
  have h := scaleRoots_eval₂_mul (RingHom.id E) ((z + A) / F) F
    (p := p.map (algebraMap k E))
  have hmul : F * ((z + A) / F) = z + A := by field_simp
  simp only [RingHom.id_apply, hmul, eval₂_id, eval_map, ← aeval_def] at h
  rw [natDegree_map] at h
  exact h

/-- Coefficient transport preserves the entire denominator-cleared numerator. -/
theorem clearedPlanePolynomial_map {S : Type*} [CommRing S] [Nontrivial S] [Algebra k S]
    (g : R →ₐ[k] S) {p : Polynomial k} (hp : p.Monic) (A F : R) :
    (clearedPlanePolynomial p A F).map g.toRingHom =
      clearedPlanePolynomial p (g A) (g F) := by
  have hlead : g (p.map (algebraMap k R)).leadingCoeff ≠ 0 := by
    rw [(hp.map (algebraMap k R)).leadingCoeff, map_one]
    exact one_ne_zero
  have hmap : (p.map (algebraMap k R)).map g.toRingHom = p.map (algebraMap k S) := by
    rw [Polynomial.map_map]
    congr 1
    exact g.comp_algebraMap
  rw [clearedPlanePolynomial, Polynomial.map_comp, Polynomial.map_scaleRoots _ _ _ hlead,
    hmap, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  rfl

end SkewCornerDescent
