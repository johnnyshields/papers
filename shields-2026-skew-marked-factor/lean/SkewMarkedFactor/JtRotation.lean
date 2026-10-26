/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.WeightedMN

/-!
# Rotation of a Jacobi–Trudi determinant

«Weighted composition covariance» (`sec:weighted-action`) of
`shields-2026-skew-marked-factor.tex`.
Since `h_{a-b} = h_{(c-b)-(c-a)}`, the determinant of the beta pair `(a, b)` is that of the
rotated pair `(c - b∘rev, c - a∘rev)`.  A row move of `(a, b)` is therefore a column move of
the rotated pair, and the weighted row-move sum of `wDeriv_jtDet` is a weighted column-move sum
of the rotated pair.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan Gluing.Plan.MN MvPolynomial

/-- The rotated beta pair. -/
def rotA {M : ℕ} (c : ℤ) (b : Fin M → ℤ) : Fin M → ℤ := fun i => c - b i.rev
def rotB {M : ℕ} (c : ℤ) (a : Fin M → ℤ) : Fin M → ℤ := fun i => c - a i.rev

theorem jtDet_rotate {M : ℕ} (c : ℤ) (a b : Fin M → ℤ) :
    jtDet (rotA c b) (rotB c a) = jtDet a b := by
  unfold jtDet
  have h : (Matrix.of fun i j : Fin M => hh (rotA c b i - rotB c a j)) =
      ((Matrix.of fun i j : Fin M => hh (a i - b j)).transpose).submatrix Fin.revPerm
        Fin.revPerm := by
    ext i j
    simp only [rotA, rotB, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
      Fin.revPerm_apply]
    congr 1; ring
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

/-- A row move of `(a, b)` is a column move of the rotated pair. -/
theorem jtDet_rowMove_rotate {M : ℕ} (c : ℤ) (a b : Fin M → ℤ) (i : Fin M) (r : ℤ) :
    jtDet (Function.update a i (a i - r)) b =
      jtDet (rotA c b) (Function.update (rotB c a) i.rev (rotB c a i.rev + r)) := by
  have e : Function.update (rotB c a) i.rev (rotB c a i.rev + r) =
      rotB c (Function.update a i (a i - r)) := by
    ext j
    by_cases h : j = i.rev
    · subst h; simp [rotB]; ring
    · have : j.rev ≠ i := fun hh => h (by rw [← hh]; simp)
      simp [rotB, Function.update_of_ne h, Function.update_of_ne this]
  rw [e, jtDet_rotate]

/-- **The weighted row-move sum is a weighted column-move sum of the rotated pair.** -/
theorem rowMove_sum_rotate {M : ℕ} (c : ℤ) (a b : Fin M → ℤ) (r : ℕ) :
    ∑ i : Fin M, ((a i - r : ℤ) : Lambda) * jtDet (Function.update a i (a i - r)) b =
      ∑ j : Fin M, ((c - rotB c a j - r : ℤ) : Lambda) *
        jtDet (rotA c b) (Function.update (rotB c a) j (rotB c a j + r)) := by
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin M))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply]
  rw [jtDet_rowMove_rotate c a b i.rev r]
  simp [rotB]

end SkewMarkedFactor
