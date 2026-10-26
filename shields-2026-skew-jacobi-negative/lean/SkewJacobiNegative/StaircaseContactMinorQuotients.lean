/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseContactMinorAlgebra
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localized coefficients for the staircase contact minors

The coefficient quotient in `cor:staircase-contact-minors` is formed in the
actual localization at the complete generator of the contact index.  Its
truncated convolution is proved without dividing by an unchecked denominator.
-/

namespace SkewJacobiNegative.StaircaseContactMinors

variable {R : Type*} [CommRing R]

/-- The first five quotient coefficients, using a specified inverse of the constant term. -/
def unitQuotientFive (u v : Fin 5 → R) (a : R) : Fin 5 → R :=
  let c0 := a * v 0
  let c1 := a * (v 1 - u 1 * c0)
  let c2 := a * (v 2 - u 1 * c1 - u 2 * c0)
  let c3 := a * (v 3 - u 1 * c2 - u 2 * c1 - u 3 * c0)
  let c4 := a * (v 4 - u 1 * c3 - u 2 * c2 - u 3 * c1 - u 4 * c0)
  ![c0,c1,c2,c3,c4]

/-- Multiplication by the original series recovers every coefficient through degree four. -/
theorem convolution_unitQuotientFive (u v : Fin 5 → R) (a : R)
    (ha : u 0 * a = 1) : convolutionFive u (unitQuotientFive u v a) = v := by
  have hmul (b : R) : u 0 * (a * b) = b := by rw [← mul_assoc,ha,one_mul]
  funext i
  fin_cases i <;>
    simp only [convolutionFive,unitQuotientFive,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hmul] <;> ring

/-- A unit constant term makes truncated coefficient convolution injective. -/
theorem convolutionFive_injective (u : Fin 5 → R) (a : R) (ha : u 0*a=1) :
    Function.Injective (convolutionFive u) := by
  have hai : a*u 0=1 := by simpa only [mul_comm] using ha
  have cancel {b c : R} (h : u 0*b=u 0*c) : b=c := by
    have hh := congrArg (fun x : R => a*x) h
    simpa only [←mul_assoc,hai,one_mul] using hh
  intro c d h
  have h0 : c 0=d 0 := by
    apply cancel
    simpa only [convolutionFive,Matrix.cons_val_zero] using congrFun h 0
  have h1 : c 1=d 1 := by
    apply cancel
    have hh := congrFun h 1
    simp only [convolutionFive,Matrix.cons_val_one,Matrix.cons_val_zero,h0] at hh
    exact add_right_cancel hh
  have h2 : c 2=d 2 := by
    apply cancel
    have hh := congrFun h 2
    simp only [convolutionFive,Matrix.cons_val,h0,h1] at hh
    exact add_right_cancel (add_right_cancel hh)
  have h3 : c 3=d 3 := by
    apply cancel
    have hh := congrFun h 3
    simp only [convolutionFive,Matrix.cons_val,h0,h1,h2] at hh
    exact add_right_cancel (add_right_cancel (add_right_cancel hh))
  have h4 : c 4=d 4 := by
    apply cancel
    have hh := congrFun h 4
    simp only [convolutionFive,Matrix.cons_val,h0,h1,h2,h3] at hh
    exact add_right_cancel (add_right_cancel (add_right_cancel (add_right_cancel hh)))
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- The quotient is the unique coefficient vector solving the truncated series equation. -/
theorem unitQuotientFive_unique (u v : Fin 5 → R) (a : R) (ha : u 0*a=1)
    (c : Fin 5 → R) (hc : convolutionFive u c=v) :
    c=unitQuotientFive u v a :=
  (convolutionFive_injective u a ha)
    (hc.trans (convolution_unitQuotientFive u v a ha).symm)

/-- The coefficient ring localized at the actual contact generator. -/
abbrev ContactLocalization (X : StaircaseFiveFamilies.ContactParameters) :=
  Localization.Away (complete (X.a + X.d))

/-- Coefficients of the first residue sequence in the contact chart. -/
noncomputable def contactU (X : StaircaseFiveFamilies.ContactParameters) :
    Fin 5 → ContactLocalization X :=
  fun j => algebraMap CompleteRing (ContactLocalization X)
    (complete (X.a + X.d + (j.val : ℤ) * X.b))

/-- Coefficients of the second residue sequence in the contact chart. -/
noncomputable def contactV (X : StaircaseFiveFamilies.ContactParameters) :
    Fin 5 → ContactLocalization X :=
  fun j => algebraMap CompleteRing (ContactLocalization X)
    (complete (X.d + (j.val : ℤ) * X.b))

/-- The inverse supplied by localization, not by a zero-denominator convention. -/
noncomputable def contactInverse (X : StaircaseFiveFamilies.ContactParameters) :
    ContactLocalization X :=
  IsLocalization.Away.invSelf (S := ContactLocalization X) (complete (X.a + X.d))

/-- The localization supplies the inverse used in the quotient recurrence. -/
theorem contact_inverse_spec (X : StaircaseFiveFamilies.ContactParameters) :
    contactU X 0 * contactInverse X = 1 := by
  simpa only [contactU,contactInverse,Fin.val_zero,Int.natCast_zero,zero_mul,add_zero]
    using IsLocalization.Away.mul_invSelf (S := ContactLocalization X)
      (complete (X.a + X.d))

/-- The actual five coefficients of the truncated localized quotient. -/
noncomputable def contactCoefficients (X : StaircaseFiveFamilies.ContactParameters) :
    Fin 5 → ContactLocalization X :=
  unitQuotientFive (contactU X) (contactV X) (contactInverse X)

/-- The actual localized coefficient vectors satisfy the truncated quotient equation. -/
theorem contact_convolution (X : StaircaseFiveFamilies.ContactParameters) :
    convolutionFive (contactU X) (contactCoefficients X) = contactV X :=
  convolution_unitQuotientFive _ _ _ (contact_inverse_spec X)

/-- The constructed localized vector is characterized by division through degree four. -/
theorem contact_coefficients_unique (X : StaircaseFiveFamilies.ContactParameters)
    (c : Fin 5 → ContactLocalization X)
    (hc : convolutionFive (contactU X) c=contactV X) : c=contactCoefficients X :=
  unitQuotientFive_unique _ _ _ (contact_inverse_spec X) c hc

/-- The constant coefficient is a unit in the stated localization. -/
theorem contact_constant_isUnit (X : StaircaseFiveFamilies.ContactParameters) :
    IsUnit (contactU X 0) := by
  simpa only [contactU,Fin.val_zero,Int.natCast_zero,zero_mul,add_zero]
    using IsLocalization.Away.algebraMap_isUnit (S := ContactLocalization X)
      (complete (X.a + X.d))

/-- Localization at this nonzero free generator preserves actual polynomial equality. -/
theorem contact_localization_injective (X : StaircaseFiveFamilies.ContactParameters) :
    Function.Injective (algebraMap CompleteRing (ContactLocalization X)) := by
  have hx : complete (X.a + X.d) ≠ 0 :=
    (complete_ne_zero_iff _).mpr (by have h1 := X.a_pos; have h2 := X.d_nonneg; omega)
  apply IsLocalization.injective (M := Submonoid.powers (complete (X.a + X.d)))
    (ContactLocalization X)
  intro y hy
  change ∃ n : ℕ, complete (X.a + X.d)^n = y at hy
  obtain ⟨n,rfl⟩ := hy
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hx)

end SkewJacobiNegative.StaircaseContactMinors
