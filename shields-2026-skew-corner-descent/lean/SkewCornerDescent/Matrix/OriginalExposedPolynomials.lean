/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualExposedRootOrders
import SkewCornerDescent.RegularDetectorSpecialization

/-!
# Original polynomial representatives of the normalized exposed responses

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:peeling`).
The original rational-coefficient numerators and square denominators map to the actual
real representatives used by the exposed coordinate slice. No source response is replaced
by an independent variable. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial SelectedCoordinate

/-- The normalized numerator remains a polynomial in surviving original generators. -/
noncomputable def originalExposedNumerator {α : Type*} (N : ℕ+) (top : α → ℕ+)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N) (a : α) : OtherPolynomial N :=
  (X ⟨top a, htop a⟩ * q a + p a) * q a

/-- Real coefficient extension gives exactly the unchanged exposed numerator. -/
theorem real_originalExposedNumerator {α : Type*} (N : ℕ+) (top : α → ℕ+)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N) (a : α) :
    realResiduePolynomial N (originalExposedNumerator N top p q htop a) =
      exposedResponseNumerator N top p q a := by
  simp [originalExposedNumerator, exposedResponseNumerator, realResiduePolynomial]

/-- The normalized source fraction is the full original monic response, including its correction. -/
theorem originalExposedNumerator_fraction {α : Type*} (N : ℕ+) (top : α → ℕ+)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N) (a : α) (hq : q a ≠ 0) :
    algebraMap (OtherPolynomial N) (OtherField N) (originalExposedNumerator N top p q htop a) /
        algebraMap (OtherPolynomial N) (OtherField N) (q a ^ 2) =
      residueGenerator N ⟨top a, htop a⟩ +
        algebraMap (OtherPolynomial N) (OtherField N) (p a) /
          algebraMap (OtherPolynomial N) (OtherField N) (q a) := by
  have hqF : algebraMap (OtherPolynomial N) (OtherField N) (q a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq
  simp only [originalExposedNumerator, map_mul, map_add, map_pow]
  change ((residueGenerator N ⟨top a, htop a⟩ * _ + _) * _) / _ = _
  field_simp

/-- Specialization is a polynomial map into the slice fraction field, not a map of the whole
original fraction field. -/
noncomputable def originalCoordinateSlice (N K : ℕ+) (x : ℕ → ℝ) :
    OtherPolynomial N →+* RatFunc ℝ :=
  (algebraMap (Polynomial ℝ) (RatFunc ℝ)).comp
    ((coordinatePolynomial (K : ℕ) x).comp (realResiduePolynomial N))

/-- The actual chamber produces regularity of every source numerator and denominator in the
slice fraction field, including the numerator whose evaluation vanishes at the exposed root. -/
theorem originalCoordinateSlice_regular {α : Type*} [Finite α]
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (htop : ∀ a, top a ≠ N)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hanchor : ∃ a, top a = K) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive) :
    (∀ a, originalCoordinateSlice N K x (originalExposedNumerator N top p q htop a) ≠ 0) ∧
      (∀ a, originalCoordinateSlice N K x (q a ^ 2) ≠ 0) := by
  classical
  obtain ⟨a, _, hsimple, hden, hsign⟩ :=
    simultaneousActualChamber_exposed_slice N K hNK top p q hp hq hanchor positive x hx
  dsimp only at hsimple hden hsign
  let slice := coordinatePolynomial (K : ℕ) x
  have hn (i : α) : slice (exposedResponseNumerator N top p q i) ≠ 0 := by
    by_cases hi : i = a.val
    · subst i
      intro hz
      rw [hz, Polynomial.rootMultiplicity_zero] at hsimple
      exact Nat.zero_ne_one hsimple
    · intro hz
      have h := hsign i hi
      rw [hz, Polynomial.eval_zero, mul_zero] at h
      exact (lt_irrefl 0) h
  have hd (i : α) : slice (exposedResponseDenominator N q i) ≠ 0 := by
    intro hz
    have h := hden i
    rw [hz, Polynomial.eval_zero] at h
    exact (lt_irrefl 0) h
  constructor
  · intro i
    simpa only [originalCoordinateSlice, RingHom.comp_apply, real_originalExposedNumerator]
      using (RatFunc.algebraMap_ne_zero (hn i))
  · intro i
    simpa only [originalCoordinateSlice, RingHom.comp_apply, map_pow,
      exposedResponseDenominator] using (RatFunc.algebraMap_ne_zero (hd i))

end SkewCornerDescent.Matrix
