/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.DiscreteInterior
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Data.Rat.Lemmas

/-!
# Associates of actual skew Schur functions

Supports `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `thm:descent`, `prop:beta-reduction`).
Integral primitivity forces a rational associate scalar to be a sign; positive
specialization forces that sign to be positive.

Sorry-free.
-/

namespace SkewGluing
open MvPolynomial

/-- The denominator of a rational scaling divides every coefficient of the source. -/
theorem denominator_dvd_coeff_of_scaling {f g : MvPolynomial ℕ+ ℤ} {q : ℚ}
    (he : map (Int.castRingHom ℚ) f * C q = map (Int.castRingHom ℚ) g)
    (m : ℕ+ →₀ ℕ) : (q.den : ℤ) ∣ f.coeff m := by
  have hc := congrArg (fun P : MvPolynomial ℕ+ ℚ => P.coeff m) he
  rw [mul_comm, coeff_C_mul, coeff_map, coeff_map] at hc
  change q * (f.coeff m : ℚ) = (g.coeff m : ℚ) at hc
  by_cases hz : f.coeff m = 0
  · rw [hz]; exact dvd_zero _
  have hz' : (f.coeff m : ℚ) ≠ 0 := by exact_mod_cast hz
  have hq : q = (g.coeff m : ℚ) / f.coeff m := by
    apply (eq_div_iff hz').mpr
    simpa only [mul_comm] using hc
  have hq' : q = Rat.divInt (g.coeff m) (f.coeff m) := by
    simpa only [Rat.divInt_eq_div] using hq
  rw [hq']
  exact Rat.den_dvd _ _

/-- Primitive integer polynomials have only signs as rational associate scalars. -/
theorem sign_of_primitive_scaling {f g : MvPolynomial ℕ+ ℤ} {q : ℚ}
    (hf : ∀ a : ℤ, (∀ m, a ∣ f.coeff m) → IsUnit a)
    (hg : ∀ a : ℤ, (∀ m, a ∣ g.coeff m) → IsUnit a)
    (he : map (Int.castRingHom ℚ) f * C q = map (Int.castRingHom ℚ) g) :
    q = 1 ∨ q = -1 := by
  have hd := hf q.den (denominator_dvd_coeff_of_scaling he)
  have hden : q.den = 1 := by
    have hdu := Int.isUnit_iff.mp hd
    have hp := q.den_pos
    omega
  have hq := Rat.coe_int_num_of_den_eq_one hden
  have hn : IsUnit q.num := hg q.num (fun m => by
    have hc := congrArg (fun P : MvPolynomial ℕ+ ℚ => P.coeff m) he
    rw [mul_comm, coeff_C_mul, coeff_map, coeff_map] at hc
    change q * (f.coeff m : ℚ) = (g.coeff m : ℚ) at hc
    rw [← hq] at hc
    have hc' : q.num * f.coeff m = g.coeff m := by exact_mod_cast hc
    exact ⟨f.coeff m, hc'.symm⟩)
  rcases Int.isUnit_iff.mp hn with hn | hn
  · left
    rw [← hq, hn]
    norm_num
  · right
    rw [← hq, hn]
    norm_num

/-- Rational associates of actual skew Schur functions are equal, not merely proportional. -/
theorem cellSchur_eq_of_associated {D E : Diagram} (hD : IsSkew D) (hE : IsSkew E)
    (ha : Associated (cellSchur D hD) (cellSchur E hE)) :
    cellSchur D hD = cellSchur E hE := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨q, _, hq⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  rw [hq] at hu
  have hi : map (Int.castRingHom ℚ) (integralCellSchur D hD) * C q =
      map (Int.castRingHom ℚ) (integralCellSchur E hE) := by
    simpa only [map_integralCellSchur] using hu
  rcases sign_of_primitive_scaling (integralCellSchur_primitive D hD)
    (integralCellSchur_primitive E hE) hi with he | he
  · simpa [he] using hu
  · have hn : cellSchur D hD = -cellSchur E hE := by
      simpa [he] using congrArg Neg.neg hu
    exact False.elim ((positiveAtOnes_cellSchur hD).ne_neg (positiveAtOnes_cellSchur hE) hn)

end SkewGluing
