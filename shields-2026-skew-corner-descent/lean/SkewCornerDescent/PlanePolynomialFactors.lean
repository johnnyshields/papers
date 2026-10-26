/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.PlanePolynomialAffine

/-!
# Divisibility and coprimality of cleared plane polynomials

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Rational numerator and denominator
factors are transported before any response factorization is inferred.

Sorry-free.
-/

namespace SkewCornerDescent

open Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Nontrivial R] [Algebra k R]

/-- Naturality applies to arbitrary rational numerators, not just monic factors. -/
theorem clearedPlanePolynomial_map_all {S : Type*} [CommRing S] [Nontrivial S]
    [Algebra k S] (g : R →ₐ[k] S) (p : Polynomial k) (A F : R) :
    (clearedPlanePolynomial p A F).map g.toRingHom =
      clearedPlanePolynomial p (g A) (g F) := by
  by_cases hp : p = 0
  · simp only [hp, clearedPlanePolynomial, Polynomial.map_zero, zero_scaleRoots, zero_comp]
  have hlead : g (p.map (algebraMap k R)).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_map_of_injective (RingHom.injective _) p]
    rw [g.commutes]
    exact (map_ne_zero (algebraMap k S)).mpr (leadingCoeff_ne_zero.mpr hp)
  have hmap : (p.map (algebraMap k R)).map g.toRingHom = p.map (algebraMap k S) := by
    rw [Polynomial.map_map]
    congr 1
    exact g.comp_algebraMap
  rw [clearedPlanePolynomial, Polynomial.map_comp, Polynomial.map_scaleRoots _ _ _ hlead,
    hmap, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  rfl

omit [Nontrivial R] in
/-- Clearing denominators preserves every polynomial factor. -/
theorem clearedPlanePolynomial_dvd [NoZeroDivisors R] {p q : Polynomial k}
    (h : p ∣ q) (A F : R) :
    clearedPlanePolynomial p A F ∣ clearedPlanePolynomial q A F := by
  exact _root_.map_dvd
    (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C A))
    (Polynomial.scaleRoots_dvd _ _ (_root_.map_dvd
      (Polynomial.mapRingHom (algebraMap k R)) h))

/-- Coprime rational polynomials stay coprime after clearing a nonzero cap denominator. -/
theorem clearedPlanePolynomial_isCoprime {E : Type*} [Field E] [Algebra k E]
    {p q : Polynomial k} (h : IsCoprime p q) (A F : E) (hF : F ≠ 0) :
    IsCoprime (clearedPlanePolynomial p A F) (clearedPlanePolynomial q A F) := by
  have hm : IsCoprime (p.map (algebraMap k E)) (q.map (algebraMap k E)) :=
    h.map (Polynomial.mapRingHom (algebraMap k E))
  have hs : IsCoprime ((p.map (algebraMap k E)).scaleRoots F)
      ((q.map (algebraMap k E)).scaleRoots F) :=
    Polynomial.isCoprime_scaleRoots _ _ F (isUnit_iff_ne_zero.mpr hF) hm
  exact hs.map (Polynomial.compRingHom (Polynomial.X + Polynomial.C A))

end SkewCornerDescent
