/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergEndLocality

/-!
# Complete logarithmic locality for finite Hessenberg matrices

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
An auxiliary infinite extension agrees with every entry of the finite matrix.
Only the extension outside the source is synthetic; every source cap jet remains.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F] {N : ℕ}

/-- Extend a finite matrix by unit diagonal states and the same selected subdiagonal.
The extension is only a device for applying finite-window locality. -/
def hessenbergExtension (A : Matrix (Fin N) (Fin N) (PowerSeries F)) (a : F)
    (i j : ℕ) : PowerSeries F :=
  if j + 1 = i then PowerSeries.C a * PowerSeries.X
  else if hi : i < N then
    if hj : j < N then A ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else if i = j then 1 else 0

/-- Every entry inside the original finite matrix is retained exactly. -/
theorem hessenbergExtension_inside (A : Matrix (Fin N) (Fin N) (PowerSeries F))
    (a : F) (hsub : ∀ i j : Fin N, j.val + 1 = i.val →
      A i j = PowerSeries.C a * PowerSeries.X) (i j : Fin N) :
    hessenbergExtension A a i.val j.val = A i j := by
  unfold hessenbergExtension
  by_cases h : j.val + 1 = i.val
  · rw [ite_eq_left h]
    exact (hsub i j h).symm
  · rw [ite_eq_right h, dite_eq_left i.isLt, dite_eq_left j.isLt]

/-- The auxiliary family retains the upper-Hessenberg support. -/
theorem hessenbergExtension_shape (A : Matrix (Fin N) (Fin N) (PowerSeries F))
    (a : F) (hA : IsUpperHessenberg A) :
    ∀ i j : ℕ, j + 1 < i → hessenbergExtension A a i j = 0 := by
  intro i j hij
  unfold hessenbergExtension
  rw [ite_eq_right (by omega)]
  split_ifs with hi hj he
  · exact hA _ _ hij
  · rfl
  · omega
  · rfl

/-- The extension has the exact original selected subdiagonal everywhere. -/
theorem hessenbergExtension_subdiag (A : Matrix (Fin N) (Fin N) (PowerSeries F))
    (a : F) (i : ℕ) :
    hessenbergExtension A a (i + 1) i = PowerSeries.C a * PowerSeries.X := by
  simp [hessenbergExtension]

/-- Nonzero diagonal residues of the finite source supply regularity of the extension. -/
theorem hessenbergExtension_regular (A : Matrix (Fin N) (Fin N) (PowerSeries F))
    (a : F) (hdiag : ∀ i : Fin N, PowerSeries.constantCoeff (A i i) ≠ 0) :
    ∀ i : ℕ, PowerSeries.constantCoeff (hessenbergExtension A a i i) ≠ 0 := by
  intro i
  unfold hessenbergExtension
  rw [ite_eq_right (by omega)]
  by_cases hi : i < N
  · rw [dite_eq_left hi, dite_eq_left hi]
    exact hdiag ⟨i, hi⟩
  · rw [dite_eq_right hi, ite_eq_left rfl]
    simp

/-- The complete finite determinant is an interval determinant of the auxiliary family. -/
theorem hessenbergExtension_det (A : Matrix (Fin N) (Fin N) (PowerSeries F))
    (a : F) (hsub : ∀ i j : Fin N, j.val + 1 = i.val →
      A i j = PowerSeries.C a * PowerSeries.X) :
    intervalDet (hessenbergExtension A a) 0 N = A.det := by
  unfold intervalDet
  congr 1
  ext i j : 1
  simp only [Matrix.of_apply, zero_add]
  exact hessenbergExtension_inside A a hsub i j

variable [Algebra ℚ F]

/-- All finite-source left endpoint log coefficients through order `k` are local to
its first `k+1` states. No diagonal normalization or fresh-generator restriction is used. -/
theorem finite_hessenberg_left_log_locality
    (A : Matrix (Fin N) (Fin N) (PowerSeries F)) (a : F)
    (hA : IsUpperHessenberg A)
    (hdiag : ∀ i : Fin N, PowerSeries.constantCoeff (A i i) ≠ 0)
    (k m : ℕ) (hkm : k ≤ m) :
    PowerSeries.coeff k (leftCap (hessenbergExtension A a) m) =
      PowerSeries.coeff k (leftCap (hessenbergExtension A a) k) := by
  exact leftCap_coeff_eq_of_le _ a (hessenbergExtension_shape A a hA)
    (hessenbergExtension_subdiag A a) (hessenbergExtension_regular A a hdiag)
    k k m le_rfl hkm

/-- All finite-source right endpoint log coefficients through order `k` are local to
its last `k+1` states, retaining the complete source entries. -/
theorem finite_hessenberg_right_log_locality
    (A : Matrix (Fin N) (Fin N) (PowerSeries F)) (a : F)
    (hA : IsUpperHessenberg A)
    (hdiag : ∀ i : Fin N, PowerSeries.constantCoeff (A i i) ≠ 0)
    (k d s : ℕ) :
    PowerSeries.coeff k (rightCap (hessenbergExtension A a) s (k + d)) =
      PowerSeries.coeff k (rightCap (hessenbergExtension A a) (s + d) k) := by
  exact rightCap_shift _ a (hessenbergExtension_shape A a hA)
    (hessenbergExtension_subdiag A a) (hessenbergExtension_regular A a hdiag) k d s

end SkewCornerDescent.Matrix
