/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.PolynomialReadings
import Mathlib.Algebra.MvPolynomial.Nilpotent
import SkewJacobiNegative.OrdinaryReadings
import SkewJacobiNegative.ConnectedIrreducibility

/-!
# Integral primitive irreducibility from the rational representation

The integral and rational irreducibility input quoted in `sec:boundary` of
`shields-2026-skew-cofactor-independence.tex`.  A coefficient-one monomial
makes every integral constant factor a unit.  Faithful coefficient extension
therefore reflects irreducibility for these primitive polynomials.
Sorry-free.
-/

namespace SkewJacobiNegative

/-- Ordinary degrees are determined by supports, so faithful extension preserves them. -/
theorem integerLift_totalDegree (p : Base.CompleteRing) :
    (integerLift p).totalDegree = p.totalDegree := by
  unfold MvPolynomial.totalDegree
  rw [integerLift_support]

/-- A factor of a coefficient-one polynomial cannot become a new unit only over the rationals. -/
theorem isUnit_of_integerLift_factor {p q : Base.CompleteRing} (d : ℕ+ →₀ ℕ)
    (hp : p.coeff d = 1) (hq : q ∣ p) (hu : IsUnit (integerLift q)) : IsUnit q := by
  have hd : q.totalDegree = 0 := by
    rw [← integerLift_totalDegree]
    exact (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
  have he : q = MvPolynomial.C (q.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  obtain ⟨r, hr⟩ := hq
  have hc := congrArg (fun f : Base.CompleteRing => f.coeff d) hr
  rw [hp, he, MvPolynomial.coeff_C_mul] at hc
  have hunit : IsUnit (q.coeff 0) := isUnit_iff_dvd_one.mpr ⟨r.coeff d, hc⟩
  rw [he]
  exact hunit.map MvPolynomial.C

/-- Rational irreducibility plus an actual coefficient-one monomial
proves integral irreducibility. -/
theorem irreducible_integer_of_integerLift (p : Base.CompleteRing) (d : ℕ+ →₀ ℕ)
    (hp : p.coeff d = 1) (hQ : Irreducible (integerLift p)) : Irreducible p where
  not_isUnit hu := hQ.not_isUnit (hu.map integerLift)
  isUnit_or_isUnit a b hab := by
    have hm : integerLift a * integerLift b = integerLift p := by
      rw [← map_mul, hab]
    rcases hQ.isUnit_or_isUnit hm.symm with ha | hb
    · exact Or.inl (isUnit_of_integerLift_factor d hp ⟨b, hab⟩ ha)
    · exact Or.inr (isUnit_of_integerLift_factor d hp ⟨a, by rw [hab, mul_comm]⟩ hb)

namespace BetaDiagram

/-- The actual integral Jacobi–Trudi determinant has a coefficient-one monomial. -/
theorem integerSchur_diagonal_coefficient_one {n : ℕ} (D : BetaDiagram n) :
    D.integerSchur.coeff D.diagonalExponent = 1 := by
  have h := D.diagonal_coefficient_one
  rw [D.schur_eq_integerLift, integerLift_coeff] at h
  exact_mod_cast h

/-- Connectedness proves irreducibility of the actual integral determinant as well. -/
theorem integerSchur_irreducible {n : ℕ} (D : BetaDiagram n) (hD : D.Connected) :
    Irreducible D.integerSchur :=
  irreducible_integer_of_integerLift D.integerSchur D.diagonalExponent
    D.integerSchur_diagonal_coefficient_one
    (D.schur_eq_integerLift ▸ D.schur_irreducible hD)

end BetaDiagram

end SkewJacobiNegative
