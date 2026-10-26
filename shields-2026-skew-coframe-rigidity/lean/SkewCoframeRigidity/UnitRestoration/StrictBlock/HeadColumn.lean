/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The inverse column of a block-triangular matrix and the strict-block identity

The linear algebra behind `sc:strict-block-variation` in
`shields-2026-skew-coframe-rigidity.tex`.  Let `T = [[P, B], [0, E]]` be block upper triangular
over a field, with pivot row the first index of `E`.  Let `S` be `T` with the pivot row replaced
by a row `τ`, and `ã` the column `v` with its pivot entry replaced by `c`.  For vectors `u`, `y`
with `T u = e_pivot` and `T y = v`, and a row `w` vanishing on the `P` columns,

* `det S = det P · det E · (τ ⬝ u)`: the top row-replacement quotient is `s_N / (det P · s_E)`;
* `-w adj(S) ã = -det S (w ⬝ y + (w ⬝ u)(c - τ ⬝ y) / (τ ⬝ u))`;
* `-w_E adj(E) v_E = -det E (w ⬝ y)`;

and therefore
`det E · (-w adj(S) ã) - det S · (-w_E adj(E) v_E) = -det P · (det E)² (w ⬝ u)(c - τ ⬝ y)`.
The `P` and `L` blocks enter only through `det P`; a restoration whose column row `w` vanishes
on `E` contributes nothing.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open Matrix

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vector solving the replaced system: `z = y + ((c - τ ⬝ y)/(τ ⬝ u)) u`. -/
theorem updateRow_mulVec_solve (T : Matrix ι ι F) (p : ι) (τ v u y : ι → F) (c : F)
    (hu : T *ᵥ u = Pi.single p 1) (hy : T *ᵥ y = v) (hσ : τ ⬝ᵥ u ≠ 0) :
    (T.updateRow p τ) *ᵥ (y + ((c - τ ⬝ᵥ y) / (τ ⬝ᵥ u)) • u) = Function.update v p c := by
  funext i
  by_cases hi : i = p
  · subst hi
    simp only [Matrix.mulVec, Matrix.updateRow_self, dotProduct_add, dotProduct_smul,
      smul_eq_mul, Function.update_self]
    field_simp
    ring
  · have h1 := congrFun hu i
    have h2 := congrFun hy i
    simp only [Matrix.mulVec, Matrix.updateRow_ne hi, dotProduct_add, dotProduct_smul,
      smul_eq_mul, Function.update_of_ne hi]
    simp only [Matrix.mulVec] at h1 h2
    rw [h2, h1, Pi.single_eq_of_ne hi]
    ring

/-- `adj(S) ã = det S · z` whenever `S z = ã`. -/
theorem adjugate_mulVec_of_mulVec_eq (S : Matrix ι ι F) (z a : ι → F) (h : S *ᵥ z = a) :
    S.adjugate *ᵥ a = S.det • z := by
  rw [← h, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **Cramer for the pivot row**: replacing the pivot row of `T` by `τ` multiplies `det T` by
`τ ⬝ u`, where `u` is the inverse column `T⁻¹ e_pivot`. -/
theorem det_updateRow_eq (T : Matrix ι ι F) (hT : T.det ≠ 0) (p : ι) (τ u : ι → F)
    (hu : T *ᵥ u = Pi.single p 1) : (T.updateRow p τ).det = T.det * (τ ⬝ᵥ u) := by
  have hTu : IsUnit T.det := hT.isUnit
  set c : ι → F := τ ᵥ* T⁻¹ with hc
  have hrow : τ = ∑ k, c k • T k := by
    funext j
    have : c ᵥ* T = τ := by
      rw [hc, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul T hTu, Matrix.vecMul_one]
    rw [← this]
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, mul_comm]
  have hdet := Matrix.det_updateRow_sum T p c
  rw [← hrow] at hdet
  rw [hdet, smul_eq_mul, mul_comm]
  congr 1
  have hu' : u = T⁻¹ *ᵥ Pi.single p 1 := by
    rw [← hu, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hTu, Matrix.one_mulVec]
  rw [hc, hu']
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.single_apply]


section Blocks

variable {κ θ : Type*} [Fintype κ] [DecidableEq κ] [Fintype θ] [DecidableEq θ]

/-- **The strict-block identity** (`sc:strict-block-variation`), for `T = [[P, B], [0, E]]`
with pivot row `p₀` of `E`.  The numerator `det S` is `det P · det E · (τ ⬝ u)`, and the
combination `det E · ṡ_S - det S · ṡ_E` collapses to `-det P (det E)² (w ⬝ u)(c - τ ⬝ y)`: the
columns of `P` and every row below `E` enter only through `det P`. -/
theorem strict_block_identity (P : Matrix κ κ F) (Bm : Matrix κ θ F) (E : Matrix θ θ F)
    (hP : P.det ≠ 0) (hE : E.det ≠ 0) (p₀ : θ) (τ v u y w : κ ⊕ θ → F) (c : F)
    (hu : (Matrix.fromBlocks P Bm 0 E) *ᵥ u = Pi.single (Sum.inr p₀) 1)
    (hy : (Matrix.fromBlocks P Bm 0 E) *ᵥ y = v) (hσ : τ ⬝ᵥ u ≠ 0)
    (hw : ∀ i, w (Sum.inl i) = 0) :
    ((Matrix.fromBlocks P Bm 0 E).updateRow (Sum.inr p₀) τ).det =
        P.det * E.det * (τ ⬝ᵥ u) ∧
    E.det * (-(w ⬝ᵥ (((Matrix.fromBlocks P Bm 0 E).updateRow (Sum.inr p₀) τ).adjugate *ᵥ
        Function.update v (Sum.inr p₀) c))) -
      ((Matrix.fromBlocks P Bm 0 E).updateRow (Sum.inr p₀) τ).det *
        (-((fun j => w (Sum.inr j)) ⬝ᵥ (E.adjugate *ᵥ fun j => v (Sum.inr j)))) =
      -(P.det * E.det ^ 2 * (w ⬝ᵥ u) * (c - τ ⬝ᵥ y)) := by
  set T := Matrix.fromBlocks P Bm 0 E with hT
  have hdetT : T.det = P.det * E.det := by
    rw [hT, Matrix.det_fromBlocks_zero₂₁]
  have hdet1 := det_updateRow_eq T (by rw [hdetT]; exact mul_ne_zero hP hE) (Sum.inr p₀) τ u hu
  rw [hdetT] at hdet1
  refine ⟨hdet1, ?_⟩
  set σ := τ ⬝ᵥ u with hσdef
  set z := y + ((c - τ ⬝ᵥ y) / σ) • u with hz
  have hSz := updateRow_mulVec_solve T (Sum.inr p₀) τ v u y c hu hy hσ
  have hadj := adjugate_mulVec_of_mulVec_eq _ z _ hSz
  rw [hadj, hdet1]
  have hyE : E *ᵥ (fun j => y (Sum.inr j)) = fun j => v (Sum.inr j) := by
    funext j
    have := congrFun hy (Sum.inr j)
    rw [← this]
    simp [hT, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]
  rw [adjugate_mulVec_of_mulVec_eq E _ _ hyE]
  have hwy : (fun j => w (Sum.inr j)) ⬝ᵥ (fun j => y (Sum.inr j)) = w ⬝ᵥ y := by
    simp [dotProduct, Fintype.sum_sum_type, hw]
  rw [dotProduct_smul, dotProduct_smul, hwy]
  simp only [hz, dotProduct_add, dotProduct_smul, smul_eq_mul]
  field_simp
  ring

end Blocks


section Poly

variable {R : Type*} [CommRing R] [IsDomain R] {ι' : Type*} [Fintype ι'] [DecidableEq ι']

omit [IsDomain R] in
theorem adjugate_mulVec_of_mulVec_eq' (S : Matrix ι' ι' R) (z a : ι' → R) (h : S *ᵥ z = a) :
    S.adjugate *ᵥ a = S.det • z := by
  rw [← h, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Cofactor expansion along the replaced row: `det (T with row p ↦ τ) = τ ⬝ (adj T)_{·p}`. -/
theorem det_updateRow_eq_dot_adjugate (T : Matrix ι' ι' R) (p : ι') (τ : ι' → R) :
    (T.updateRow p τ).det = τ ⬝ᵥ (T.adjugate *ᵥ Pi.single p 1) := by
  rw [Matrix.det_eq_sum_mul_adjugate_row (T.updateRow p τ) p]
  simp only [Matrix.updateRow_self, dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply, Matrix.updateRow_idem]

omit [IsDomain R] in
/-- The scaled solution of the replaced system, with `u = adj T e_p` and `y = adj T v`. -/
theorem updateRow_mulVec_scaled (T : Matrix ι' ι' R) (p : ι') (τ v u y : ι' → R) (c : R)
    (hu : T *ᵥ u = T.det • Pi.single p 1) (hy : T *ᵥ y = T.det • v) :
    (T.updateRow p τ) *ᵥ ((τ ⬝ᵥ u) • y + (c * T.det - τ ⬝ᵥ y) • u) =
      (T.det * (τ ⬝ᵥ u)) • Function.update v p c := by
  funext i
  by_cases hi : i = p
  · subst hi
    simp only [Matrix.mulVec, Matrix.updateRow_self, dotProduct_add, dotProduct_smul,
      smul_eq_mul, Pi.smul_apply, Function.update_self]
    ring
  · have h1 := congrFun hu i
    have h2 := congrFun hy i
    simp only [Matrix.mulVec, Matrix.updateRow_ne hi, dotProduct_add, dotProduct_smul,
      smul_eq_mul, Pi.smul_apply, Function.update_of_ne hi]
    simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [h2, h1, Pi.single_eq_of_ne hi]
    ring

variable {κ θ : Type*} [Fintype κ] [DecidableEq κ] [Fintype θ] [DecidableEq θ]

/-- **The strict-block identity, polynomial form.**  With `D = det T = det P · det E`,
`u = adj T e_{p₀}`, `y = adj T v` and `S` the replaced matrix with `det S ≠ 0`,
`D (det E · ṡ_S - det S · ṡ_E) = - det E (w ⬝ u)(c D - τ ⬝ y)`. -/
theorem strict_block_identity_poly (P : Matrix κ κ R) (Bm : Matrix κ θ R) (E : Matrix θ θ R)
    (p₀ : θ) (τ v w : κ ⊕ θ → R) (c : R)
    (hS : ((Matrix.fromBlocks P Bm 0 E).updateRow (Sum.inr p₀) τ).det ≠ 0)
    (hw : ∀ i, w (Sum.inl i) = 0) :
    (Matrix.fromBlocks P Bm 0 E).det *
      (E.det * (-(w ⬝ᵥ (((Matrix.fromBlocks P Bm 0 E).updateRow (Sum.inr p₀) τ).adjugate *ᵥ
          Function.update v (Sum.inr p₀) c))) -
        ((Matrix.fromBlocks P Bm 0 E).updateRow (Sum.inr p₀) τ).det *
          (-((fun j => w (Sum.inr j)) ⬝ᵥ (E.adjugate *ᵥ fun j => v (Sum.inr j))))) =
      -(E.det * (w ⬝ᵥ ((Matrix.fromBlocks P Bm 0 E).adjugate *ᵥ Pi.single (Sum.inr p₀) 1)) *
        (c * (Matrix.fromBlocks P Bm 0 E).det -
          τ ⬝ᵥ ((Matrix.fromBlocks P Bm 0 E).adjugate *ᵥ v))) := by
  set T := Matrix.fromBlocks P Bm 0 E with hT
  set u := T.adjugate *ᵥ (Pi.single (Sum.inr p₀) 1 : κ ⊕ θ → R) with hu
  set y := T.adjugate *ᵥ v with hy
  have hu' : T *ᵥ u = T.det • Pi.single (Sum.inr p₀) 1 := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hy' : T *ᵥ y = T.det • v := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdetS : (T.updateRow (Sum.inr p₀) τ).det = τ ⬝ᵥ u :=
    det_updateRow_eq_dot_adjugate T _ τ
  set S := T.updateRow (Sum.inr p₀) τ with hSdef
  set σ' := τ ⬝ᵥ u with hσ'
  set z := σ' • y + (c * T.det - τ ⬝ᵥ y) • u with hz
  have hSz := updateRow_mulVec_scaled T (Sum.inr p₀) τ v u y c hu' hy'
  -- `D adj S ã = z`
  have hkey : T.det • (S.adjugate *ᵥ Function.update v (Sum.inr p₀) c) = z := by
    have h1 : S.adjugate *ᵥ (S *ᵥ z) = S.det • z := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hSz, Matrix.mulVec_smul, hdetS] at h1
    have h2 : σ' • (T.det • (S.adjugate *ᵥ Function.update v (Sum.inr p₀) c)) = σ' • z := by
      rw [smul_smul, mul_comm]
      exact h1
    exact smul_right_injective _ (hdetS ▸ hS) h2
  -- the `E` side
  have hyE : E *ᵥ (fun j => y (Sum.inr j)) = T.det • fun j => v (Sum.inr j) := by
    funext j
    have := congrFun hy' (Sum.inr j)
    simp only [Pi.smul_apply, smul_eq_mul] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← this]
    simp [hT, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]
  have hE' : T.det • (E.adjugate *ᵥ fun j => v (Sum.inr j)) =
      E.det • fun j => y (Sum.inr j) := by
    have := adjugate_mulVec_of_mulVec_eq' E _ _ hyE
    rwa [Matrix.mulVec_smul] at this
  have hwy : (fun j => w (Sum.inr j)) ⬝ᵥ (fun j => y (Sum.inr j)) = w ⬝ᵥ y := by
    simp [dotProduct, Fintype.sum_sum_type, hw]
  have e1 : T.det * (w ⬝ᵥ (S.adjugate *ᵥ Function.update v (Sum.inr p₀) c)) = w ⬝ᵥ z := by
    rw [← hkey, dotProduct_smul, smul_eq_mul]
  have e2 : T.det * ((fun j => w (Sum.inr j)) ⬝ᵥ (E.adjugate *ᵥ fun j => v (Sum.inr j))) =
      E.det * (w ⬝ᵥ y) := by
    have := congrArg (fun q => (fun j => w (Sum.inr j)) ⬝ᵥ q) hE'
    simp only [dotProduct_smul, smul_eq_mul, hwy] at this
    exact this
  have hz' : w ⬝ᵥ z = σ' * (w ⬝ᵥ y) + (c * T.det - τ ⬝ᵥ y) * (w ⬝ᵥ u) := by
    simp only [hz, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hSdet : S.det = σ' := hdetS
  rw [hSdet]
  linear_combination (-E.det) * e1 + σ' * e2 - E.det * hz'

end Poly

end SkewCoframeRigidity.UnitRestoration
