/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.Lowering
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Inflation as a homogeneous shift on boards without index minus one

Formalizes the raising identity inside `lem:zero-free-bijection` in
`shields-2026-skew-class-inflation.tex`:
\(s_{\mathcal I(T)}=h_1^{r(T)}s_T(h_j\mapsto h_{j+1}/h_1)\) on a board with no Jacobi--Trudi
index equal to \(-1\).  The substitution lands in the fraction field of the complete-generator
ring, and the conclusion that equal determinants stay equal under a unit shift is returned to
the ring itself.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The fraction field of the rational complete-generator ring. -/
abbrev CompleteField : Type := FractionRing CompleteRing

/-- The first complete generator, viewed in the fraction field. -/
noncomputable def hOne : CompleteField := algebraMap CompleteRing CompleteField (complete 1)

theorem hOne_ne_zero : hOne ≠ 0 := by
  unfold hOne
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective CompleteRing CompleteField)]
  rw [complete_of_pos (by norm_num : (0 : ℤ) < 1)]
  exact MvPolynomial.X_ne_zero _

/-- The substitution \(h_j\mapsto h_{j+1}/h_1\). -/
noncomputable def shiftDown : CompleteRing →ₐ[ℚ] CompleteField :=
  MvPolynomial.aeval fun k : ℕ+ =>
    algebraMap CompleteRing CompleteField (complete ((k : ℕ) + 1 : ℤ)) * hOne⁻¹

/-- Every complete entry other than index minus one is a unit shift of its image. -/
theorem hOne_mul_shiftDown (a : ℤ) (ha : a ≠ -1) :
    hOne * shiftDown (complete a) = algebraMap CompleteRing CompleteField (complete (a + 1)) := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · have h2 : a + 1 < 0 := by omega
    rw [complete_of_neg h, complete_of_neg h2]
    simp
  · rw [complete_zero, map_one, mul_one]
    rfl
  · let j : ℕ+ := ⟨a.toNat, by omega⟩
    have hc : complete a = MvPolynomial.X j := complete_of_pos h
    have hj : ((j : ℕ) : ℤ) = a := by change (a.toNat : ℤ) = a; omega
    rw [hc, shiftDown, MvPolynomial.aeval_X, hj, ← mul_assoc, mul_comm hOne, mul_assoc,
      mul_inv_cancel₀ hOne_ne_zero, mul_one]

/-- The determinant of a unit-shifted board is the homogeneous shift of the original
determinant, when no entry has index minus one. -/
theorem det_shift {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (h : ∀ i j, A i j ≠ -1) :
    algebraMap CompleteRing CompleteField
        (Matrix.of fun i j => complete (A i j + 1)).det =
      hOne ^ Fintype.card ι * shiftDown (Matrix.of fun i j => complete (A i j)).det := by
  have h1 : algebraMap CompleteRing CompleteField
      (Matrix.of fun i j => complete (A i j + 1)).det =
      (hOne • (Matrix.of fun i j => shiftDown (complete (A i j)))).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    exact (hOne_mul_shiftDown _ (h i j)).symm
  rw [h1, Matrix.det_smul]
  congr 1
  rw [AlgHom.map_det]
  rfl

end SkewClassInflation
