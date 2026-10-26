/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Linear systems with a zero lower-left block

If a square matrix `T` over a field vanishes below row `q` in the columns left of `q` (a cut) and is
invertible, then both its leading `q × q` block and its trailing block are injective.  These are the
two uniqueness statements used throughout the descent in the proof of `sc:fixed-cap` of
`shields-2026-skew-coframe-rigidity.tex`.  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- `T` vanishes in the rows `≥ q` of the columns `< q`. -/
def LowerZero (T : Matrix (Fin n) (Fin n) F) (q : ℕ) : Prop :=
  ∀ i j : Fin n, q ≤ i.val → j.val < q → T i j = 0

/-- **Leading injectivity.**  A vector supported left of the cut whose image vanishes in the
leading rows is zero. -/
theorem lead_inj {T : Matrix (Fin n) (Fin n) F} {q : ℕ} (hT : T.det ≠ 0) (hq : LowerZero T q)
    (u : Fin n → F) (hu : ∀ j : Fin n, q ≤ j.val → u j = 0)
    (h : ∀ i : Fin n, i.val < q → (T *ᵥ u) i = 0) : u = 0 := by
  refine Matrix.eq_zero_of_mulVec_eq_zero hT ?_
  funext i
  by_cases hi : i.val < q
  · exact h i hi
  · simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j.val < q
    · rw [hq i j (not_lt.1 hi) hj, zero_mul]
    · rw [hu j (not_lt.1 hj), mul_zero]

/-- **Trailing injectivity.**  A vector supported right of the cut whose image vanishes in the
trailing rows is zero. -/
theorem trail_inj {T : Matrix (Fin n) (Fin n) F} {q : ℕ} (hT : T.det ≠ 0) (hq : LowerZero T q)
    (u : Fin n → F) (hu : ∀ j : Fin n, j.val < q → u j = 0)
    (h : ∀ i : Fin n, q ≤ i.val → (T *ᵥ u) i = 0) : u = 0 := by
  classical
  have hdet := Matrix.twoBlockTriangular_det T (fun i : Fin n => i.val < q)
    (fun i hi j hj => hq i j (not_lt.1 hi) hj)
  have hne : (Matrix.toSquareBlockProp T fun i : Fin n => ¬ i.val < q).det ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdet; exact hT hdet
  let v : {i : Fin n // ¬ i.val < q} → F := fun i => u i
  have hv : (Matrix.toSquareBlockProp T fun i : Fin n => ¬ i.val < q) *ᵥ v = 0 := by
    funext i
    have := h i (not_lt.1 i.2)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this ⊢
    rw [← this]
    have e1 := Finset.sum_subtype (s := Finset.univ.filter fun j : Fin n => ¬ j.val < q)
      (p := fun j : Fin n => ¬ j.val < q) (F := Subtype.fintype _) (by simp)
      (fun j : Fin n => T i j * u j)
    have e2 := Finset.sum_filter_of_ne (s := (Finset.univ : Finset (Fin n)))
      (p := fun j : Fin n => ¬ j.val < q) (f := fun j => T i j * u j) (fun j _ hj => by
        intro hlt; exact hj (by rw [hu j hlt, mul_zero]))
    rw [← e2, e1]
    rfl
  have := Matrix.eq_zero_of_mulVec_eq_zero hne hv
  funext j
  by_cases hj : j.val < q
  · exact hu j hj
  · exact congrFun this ⟨j, hj⟩

end SkewCoframeRigidity.FixedCap
