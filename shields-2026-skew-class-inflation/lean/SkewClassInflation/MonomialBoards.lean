/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.NoEscape
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Monomial obstructions for full beta boards

The connected-block obstruction in `lem:hessenberg-membership` of
`shields-2026-skew-class-inflation.tex`.  A connected determinant of order
at least two cannot be a monomial: its irreducibility would make it divide
one generator, contradicting its actual ordinary degree.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative
open scoped BigOperators

/-- A single nonzero complete-generator monomial, with its scalar coefficient retained. -/
def IsMonomial (p : CompleteRing) : Prop :=
  ∃ (d : ℕ+ →₀ ℕ) (c : ℚ), c ≠ 0 ∧ p = MvPolynomial.monomial d c

/-- A factor of a nonzero monomial is itself a nonzero monomial. -/
theorem isMonomial_of_dvd {p q : CompleteRing} (hp : p ∣ q) (hq : IsMonomial q) :
    IsMonomial p := by
  obtain ⟨d, c, hc, rfl⟩ := hq
  obtain ⟨e, b, _, hb, he⟩ := (MvPolynomial.dvd_monomial_iff_exists hc).mp hp
  refine ⟨e, b, ?_, he⟩
  intro hz
  rw [hz] at hb
  exact hc (zero_dvd_iff.mp hb)

/-- Monomiality of a product is equivalent to monomiality of each nonzero factor. -/
theorem isMonomial_mul_iff (p q : CompleteRing) :
    IsMonomial (p * q) ↔ IsMonomial p ∧ IsMonomial q := by
  constructor
  · intro h
    exact ⟨isMonomial_of_dvd (dvd_mul_right p q) h,
      isMonomial_of_dvd (dvd_mul_left q p) h⟩
  · rintro ⟨⟨d, c, hc, rfl⟩, ⟨e, b, hb, rfl⟩⟩
    exact ⟨d + e, c * b, mul_ne_zero hc hb, MvPolynomial.monomial_mul_monomial⟩

/-- An irreducible nonzero monomial can have ordinary degree at most one. -/
theorem irreducible_monomial_degree_le_one (p : CompleteRing) (hp : Irreducible p)
    (hm : IsMonomial p) : p.totalDegree ≤ 1 := by
  classical
  obtain ⟨d, c, hc, he⟩ := hm
  have hprime : Prime p := hp.prime
  have hd : p ∣ MvPolynomial.C c * ∏ i ∈ d.support, MvPolynomial.X i ^ d i := by
    change p ∣ MvPolynomial.C c * d.prod (fun i e => MvPolynomial.X i ^ e)
    rw [← MvPolynomial.monomial_eq, ← he]
  have hnot : ¬ p ∣ MvPolynomial.C c := by
    intro h
    apply hp.not_isUnit
    exact isUnit_of_dvd_unit h ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C)
  have hprod := (hprime.dvd_or_dvd hd).resolve_left hnot
  obtain ⟨i, _, hi⟩ :=
    (hprime.dvd_finsetProd_iff (fun i => MvPolynomial.X i ^ d i)).mp hprod
  have hX := hprime.dvd_of_dvd_pow hi
  have hdeg := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hX (MvPolynomial.X_ne_zero i)
  simpa only [MvPolynomial.totalDegree_X] using hdeg

/-- A connected full determinant of order at least two has more than one monomial. -/
theorem connected_schur_not_monomial {n : ℕ} (D : BetaDiagram n)
    (hD : D.Connected) (hn : 2 ≤ n) : ¬ IsMonomial D.schur := by
  intro hm
  have hd := irreducible_monomial_degree_le_one D.schur (D.schur_irreducible hD) hm
  rw [D.schur_totalDegree] at hd
  omega

end SkewClassInflation
