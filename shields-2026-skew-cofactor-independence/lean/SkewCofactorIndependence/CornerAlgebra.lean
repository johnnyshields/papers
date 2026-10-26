/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.PolynomialReadings
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# The polynomial step of connected Schur irreducibility

The algebraic producer used for the irreducibility input in `sec:boundary` of
`shields-2026-skew-cofactor-independence.tex`.  A condensation identity and
strict weighted-degree bounds force the corner coefficient and residual to
be relatively prime.  The result is a genuine linear-in-a-private-variable
irreducibility criterion; diagram inductions must supply its minor hypotheses.
Sorry-free.
-/

namespace SkewCofactorIndependence

/-- Reverse generator-index weight, so its support minimum is minus weighted degree. -/
def reverseIndexWeight (j : ℕ+) : ℝ := -(j.val : ℝ)

/-- Every monomial has nonpositive reverse generator-index weight. -/
theorem reverseIndexWeight_monomial_nonpos (d : ℕ+ →₀ ℕ) :
    Finsupp.weight reverseIndexWeight d ≤ 0 := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_nonpos
  intro j hj
  exact nsmul_nonpos (neg_nonpos.mpr (by positivity)) _

/-- A nonzero polynomial has nonpositive least reverse weight. -/
theorem reverseIndexWeight_least_nonpos (p : CompleteRing) (hp : p ≠ 0) :
    Base.leastWeight reverseIndexWeight p ≤ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hp
  exact (Base.leastWeight_lowerBound reverseIndexWeight p d hd).trans
    (reverseIndexWeight_monomial_nonpos d)

/-- A nonzero homogeneous polynomial cannot divide one of strictly smaller weighted degree. -/
theorem reverseIndexWeight_degree_lt_not_dvd {p q : CompleteRing} {a b : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hpa : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight p (-a))
    (hqb : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight q (-b))
    (hba : b < a) : ¬ p ∣ q := by
  rintro ⟨r, hr⟩
  have hrn : r ≠ 0 := by
    intro hz
    apply hq
    simp [hr, hz]
  have hm := Base.leastWeight_mul (w := reverseIndexWeight) hp hrn
  rw [← hr, Base.leastWeight_eq_of_homogeneous hq hqb,
    Base.leastWeight_eq_of_homogeneous hp hpa] at hm
  have hn := reverseIndexWeight_least_nonpos r hrn
  linarith

/-- Condensation excludes every prime common factor of the corner coefficient and residual. -/
theorem corner_isRelPrime_of_condensation
    (p c r J L R d : CompleteRing) (v : ℕ+) (a b e : ℝ)
    (hc : c ≠ 0) (hL : Irreducible L) (hR : Irreducible R)
    (hca : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight c (-a))
    (hLb : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight L (-b))
    (hRe : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight R (-e))
    (hab : a < b) (hae : a < e)
    (hsplit : p = c * MvPolynomial.X v + r)
    (hcond : p * J = L * R - c * d) : IsRelPrime c r := by
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hc).mpr
  intro f hfc hfr hf
  have hfp : f ∣ p := by
    rw [hsplit]
    exact dvd_add (dvd_mul_of_dvd_left hfc _) hfr
  have he : p * J + c * d = L * R := by
    rw [hcond]
    ring
  have hprod : f ∣ L * R := by
    rw [← he]
    exact dvd_add (dvd_mul_of_dvd_left hfp _) (dvd_mul_of_dvd_left hfc _)
  rcases hf.dvd_or_dvd hprod with hfl | hfr'
  · have hlf : L ∣ f := hf.irreducible.dvd_symm hL hfl
    exact reverseIndexWeight_degree_lt_not_dvd hL.ne_zero hc hLb hca hab (hlf.trans hfc)
  · have hrf : R ∣ f := hf.irreducible.dvd_symm hR hfr'
    exact reverseIndexWeight_degree_lt_not_dvd hR.ne_zero hc hRe hca hae (hrf.trans hfc)

/-- A private corner variable and the proved condensation coprimality yield irreducibility. -/
theorem irreducible_corner_of_condensation
    (p c r J L R d : CompleteRing) (v : ℕ+) (a b e : ℝ)
    (hc : c ≠ 0) (hL : Irreducible L) (hR : Irreducible R)
    (hca : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight c (-a))
    (hLb : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight L (-b))
    (hRe : MvPolynomial.IsWeightedHomogeneous reverseIndexWeight R (-e))
    (hab : a < b) (hae : a < e) (hvc : v ∉ c.vars) (hvr : v ∉ r.vars)
    (hsplit : p = c * MvPolynomial.X v + r)
    (hcond : p * J = L * R - c * d) : Irreducible p := by
  have hcop := corner_isRelPrime_of_condensation p c r J L R d v a b e
    hc hL hR hca hLb hRe hab hae hsplit hcond
  rw [hsplit]
  exact MvPolynomial.irreducible_mul_X_add c r v hc hvc hvr hcop

end SkewCofactorIndependence
