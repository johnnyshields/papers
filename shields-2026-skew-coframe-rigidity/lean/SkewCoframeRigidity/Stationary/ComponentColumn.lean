/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Components
import SkewCoframeRigidity.Coframe.Coherent
import SkewCoframeRigidity.Coframe.Algebra
import SkewCoframeRigidity.Stationary.LowerField

/-!
# The inverse column selected by the top row

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:component-column`.  The first column
of the inverse of the proper matrix of a connected diagram vanishes below the highest strict
component, and on the component it is `k⁻¹ (g, 1)`, where `g` is the component's own coframe
and `k = [Hg]_L` its top quotient (for a unit, `g = 1` and `k = ϑ`).
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- A vector supported on the first block that solves the block's equations is a multiple of the
first inverse column. -/
theorem mulVec_first_block {K : Type*} [Field K] (T : Matrix (Fin n) (Fin n) K) (b : Fin n → ℕ)
    (hT : ∀ i j, b j < b i → T i j = 0) (i0 : Fin n) (hi0 : ∀ i, b i0 ≤ b i)
    (w : Fin n → K) (hw : ∀ j, w j ≠ 0 → b j = b i0) (k : K) (hk : k ≠ 0)
    (hrows : ∀ i, b i = b i0 → i ≠ i0 → (T *ᵥ w) i = 0) (hrow0 : (T *ᵥ w) i0 = k) :
    T *ᵥ (k⁻¹ • w) = Pi.single i0 1 := by
  ext i
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = i0
  · subst hi; simp [hrow0, hk]
  · rw [Pi.single_eq_of_ne hi]
    by_cases hb : b i = b i0
    · rw [hrows i hb hi, mul_zero]
    · have hlt : b i0 < b i := lt_of_le_of_ne (hi0 i) (Ne.symm hb)
      have : (T *ᵥ w) i = 0 := by
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hwj : w j = 0
        · rw [hwj, mul_zero]
        · rw [hT i j (by rw [hw j hwj]; exact hlt), zero_mul]
      rw [this, mul_zero]

/-- The native equations of a connected diagram. -/
theorem properMatrix_mulVec_coframeVec {m : ℕ} {E : BetaDiagram (m + 1)} (hE : E.Connected) :
    properMatrixOf cohLetters E *ᵥ coframeVecOf cohLetters E = -topVecOf cohLetters E := by
  have hu : IsUnit (properMatrixOf cohLetters E).det :=
    (properDet_cohLetters_ne_zero hE).isUnit
  unfold coframeVecOf
  rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

/-- The first coframe equations of a connected diagram, as rows of the full matrix applied to
`(g, 1)`: zero below the top row, and the top quotient on the top row. -/
theorem full_rows {t : ℕ} {E : BetaDiagram (t + 1)} (hE : E.Connected) :
    (∀ i : Fin t, ∑ j, fullMatrixOf cohLetters E i.succ j *
        (Fin.snoc (α := fun _ => CohField) (coframeVecOf cohLetters E) 1 : Fin (t + 1) → CohField) j
        = 0) ∧
      ∑ j, fullMatrixOf cohLetters E 0 j *
        (Fin.snoc (α := fun _ => CohField) (coframeVecOf cohLetters E) 1 : Fin (t + 1) → CohField) j
        = topQuotient E := by
  have hnat := properMatrix_mulVec_coframeVec hE
  refine ⟨fun i => ?_, ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_one]
    have := congrFun hnat i
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at this
    have e2 : fullMatrixOf cohLetters E i.succ (Fin.last t) = topVecOf cohLetters E i := rfl
    rw [e2]
    have e : ∀ j : Fin t, fullMatrixOf cohLetters E i.succ j.castSucc =
        properMatrixOf cohLetters E i j := fun j => rfl
    simp only [e]
    linear_combination this
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_one]
    have h1 := coeff_span cohLetters E (coframeVecOf cohLetters E)
    have h2 : topQuotient E = PowerSeries.coeff (span E)
        (PowerSeries.mk cohLetters * (uniPoly (coframeVecOf cohLetters E) (colPos E) :
          PowerSeries CohField)) := rfl
    rw [h2, h1]
    have e : ∀ j : Fin t, fullMatrixOf cohLetters E 0 j.castSucc =
        letterOf cohLetters (E.row 0 - E.col j.castSucc) := fun j => rfl
    simp only [e]
    have e2 : fullMatrixOf cohLetters E 0 (Fin.last t) =
        letterOf cohLetters E.largestLabel := rfl
    rw [e2]
    simp only [mul_comm]
    ring

end SkewCoframeRigidity.Coframe
