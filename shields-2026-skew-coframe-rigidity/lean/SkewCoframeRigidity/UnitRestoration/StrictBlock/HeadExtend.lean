/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Extending by zero across a closing cut

Let `T` be a square matrix over a field, `ε : ι → Fin n` an injection onto the indices below `q`,
and suppose a cut at `q`: `T i j = 0` for `i ≥ q` and `j < q`.  For a vector `y` on `ι`, its
extension by zero `T`-solves exactly like `A = T.submatrix ε ε`:

* `(T ext y) (ε a) = (A y) a` and `(T ext y) i = 0` for `i ≥ q`;
* if `T` is invertible and `A` is invertible, and `r` vanishes at `i ≥ q`, then
  `T⁻¹ r = ext (A⁻¹ (r ∘ ε))`: the inverse column has no component below the cut.

Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open Matrix

variable {F : Type*} [Field F] {n q : ℕ} {ι : Type*} [Fintype ι]

/-- The extension of `y` by zero along `ε`. -/
noncomputable def extZero (ε : ι → Fin n) (y : ι → F) : Fin n → F :=
  open Classical in fun i => if h : ∃ a, ε a = i then y h.choose else 0

variable {ε : ι → Fin n}

theorem extZero_apply (hε : Function.Injective ε) (y : ι → F) (a : ι) :
    extZero ε y (ε a) = y a := by
  classical
  have h : ∃ b, ε b = ε a := ⟨a, rfl⟩
  unfold extZero
  rw [dif_pos h]
  exact congrArg y (hε h.choose_spec)

theorem extZero_of_not_range (y : ι → F) {i : Fin n} (h : ¬ ∃ a, ε a = i) :
    extZero ε y i = 0 := by
  classical
  unfold extZero; rw [dif_neg h]

theorem sum_extZero (hε : Function.Injective ε) (y : ι → F) (c : Fin n → F) :
    ∑ j, c j * extZero ε y j = ∑ a, c (ε a) * y a := by
  symm
  refine Fintype.sum_of_injective ε hε (fun a => c (ε a) * y a) (fun j => c j * extZero ε y j)
    (fun i hi => ?_) (fun a => ?_)
  · rw [extZero_of_not_range y (by simpa using hi), mul_zero]
  · rw [extZero_apply hε]

variable (hε : Function.Injective ε) (hrange : ∀ i : Fin n, i.val < q ↔ ∃ a, ε a = i)

include hrange in
theorem extZero_eq_zero_of_ge (y : ι → F) {i : Fin n} (hi : q ≤ i.val) : extZero ε y i = 0 :=
  extZero_of_not_range y (fun h => absurd ((hrange i).mpr h) (by omega))

include hε hrange in
theorem mulVec_extZero (T : Matrix (Fin n) (Fin n) F) (hcut : ∀ i j : Fin n, q ≤ i.val → j.val < q →
    T i j = 0) (y : ι → F) :
    (∀ a, (T *ᵥ extZero ε y) (ε a) = (T.submatrix ε ε *ᵥ y) a) ∧
      ∀ i : Fin n, q ≤ i.val → (T *ᵥ extZero ε y) i = 0 := by
  refine ⟨fun a => ?_, fun i hi => ?_⟩
  · simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    exact sum_extZero hε y (fun j => T (ε a) j)
  · simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j.val < q
    · rw [hcut i j hi hj, zero_mul]
    · rw [extZero_eq_zero_of_ge hrange y (by omega), mul_zero]

include hε hrange in
theorem inv_mulVec_eq_extZero [DecidableEq ι] (T : Matrix (Fin n) (Fin n) F) (hT : T.det ≠ 0)
    (hA : (T.submatrix ε ε).det ≠ 0)
    (hcut : ∀ i j : Fin n, q ≤ i.val → j.val < q → T i j = 0) (r : Fin n → F)
    (hr : ∀ i : Fin n, q ≤ i.val → r i = 0) :
    T⁻¹ *ᵥ r = extZero ε ((T.submatrix ε ε)⁻¹ *ᵥ (fun a => r (ε a))) := by
  set y := (T.submatrix ε ε)⁻¹ *ᵥ (fun a => r (ε a)) with hy
  have hAy : T.submatrix ε ε *ᵥ y = fun a => r (ε a) := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA),
      Matrix.one_mulVec]
  obtain ⟨h1, h2⟩ := mulVec_extZero hε hrange T hcut y
  have hsol : T *ᵥ extZero ε y = r := by
    funext i
    by_cases hi : i.val < q
    · obtain ⟨a, rfl⟩ := (hrange i).mp hi
      rw [h1, hAy]
    · rw [h2 i (by omega), hr i (by omega)]
  rw [← hsol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hT),
    Matrix.one_mulVec]

end SkewCoframeRigidity.UnitRestoration
