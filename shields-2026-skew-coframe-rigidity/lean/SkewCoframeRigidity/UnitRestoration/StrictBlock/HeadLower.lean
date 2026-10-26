/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadData
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadField
import SkewCoframeRigidity.UnitRestoration.Variation
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The lower block of the proper matrix and the numerator coefficients

For a closed prefix of `p` proper indices of a connected zero-free normalized board `B`, the
proper matrix `T` over the raw field vanishes below the prefix and left of the lower block, so
`T = [[P, *], [0, T_low]]`.  The lower coframe coefficients `g_j`, `j ≥ p`, solve
`T_low g_low = -f_low` with entries and right-hand side of letters of index at most the head row
`t`; hence they lie in `letterField (t + 1)`, and so do the numerator coefficients
`P_b = h_b + w_b ⬝ g` at every position `b < t`.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.FixedCap Matrix

section Subfield

variable {K : Type*} [Field K] (S : Subfield K) {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_mem_subfield' (A : Matrix ι ι K) (hA : ∀ i j, A i j ∈ S) : A.det ∈ S := by
  rw [Matrix.det_apply]
  refine Subfield.sum_mem _ fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp only [h] <;>
    simp [Subfield.prod_mem, hA, Subfield.neg_mem, Subfield.prod_mem _ fun i _ => hA _ _]

theorem inv_entry_mem_subfield' (A : Matrix ι ι K) (hA : ∀ i j, A i j ∈ S) (i j : ι) :
    A⁻¹ i j ∈ S := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul,
    Ring.inverse_eq_inv']
  refine S.mul_mem (S.inv_mem (det_mem_subfield' S A hA)) (det_mem_subfield' S _ fun p q => ?_)
  by_cases h : p = j
  · subst h
    by_cases hq : q = i <;> simp [hq, S.one_mem, S.zero_mem]
  · simp [Matrix.updateRow_ne h, hA]

end Subfield

variable {n p : ℕ}

section Lower

variable (B : BetaDiagram (n + 1)) (hpe : p + 1 ≤ n)

/-- The two-block grading of the proper indices at the cut `p`. -/
def cutGrade (p : ℕ) (i : Fin n) : ℕ := if i.val < p then 0 else 1

include hpe in
theorem properMatrix_lowerLeft (hcut : PrefixCut B p hpe) (i j : Fin n) (hi : p ≤ i.val)
    (hj : j.val < p) : properMatrixOf cohLetters B i j = 0 := by
  have hp : 0 < p := by omega
  have h1 := hcut hp
  have h2 : B.row i.succ ≤ B.row ⟨p + 1, by omega⟩ :=
    B.row_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only [Fin.val_succ]; omega)
  have h3 : B.col ⟨p - 1, by omega⟩ ≤ B.col j.castSucc :=
    B.col_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only [Fin.val_castSucc]; omega)
  simp only [properMatrixOf, Matrix.of_apply, letterOf]
  rw [if_pos (by omega)]

include hpe in
theorem properMatrix_blockTriangular (hcut : PrefixCut B p hpe) :
    (properMatrixOf cohLetters B).BlockTriangular (cutGrade p) := by
  intro i j hij
  unfold cutGrade at hij
  split_ifs at hij with h1 h2 <;> try omega
  exact properMatrix_lowerLeft B hpe hcut i j (by omega) (by omega)


theorem letterOf_mem_letterField {M : ℕ} {z : ℤ} (hz : z < M) :
    letterOf cohLetters z ∈ letterField M := by
  unfold letterOf
  split_ifs with h
  · exact Subfield.zero_mem _
  · exact cohLetters_mem_letterField (by omega)

include hpe in
theorem det_lower_ne_zero (hBc : B.Connected) (hcut : PrefixCut B p hpe) :
    ((properMatrixOf cohLetters B).toSquareBlock (cutGrade p) 1).det ≠ 0 := by
  have hT := properDet_cohLetters_ne_zero hBc
  have hdet := (properMatrix_blockTriangular B hpe hcut).det
  have h1 : (1 : ℕ) ∈ (Finset.univ : Finset (Fin n)).image (cutGrade p) :=
    Finset.mem_image.mpr ⟨⟨p, by omega⟩, Finset.mem_univ _, by simp [cutGrade]⟩
  rw [hdet] at hT
  exact fun h => hT (Finset.prod_eq_zero h1 h)

include hpe in
/-- The lower coframe coefficients lie in the field of the letters below the head row. -/
theorem lower_coframe_mem (hB : IsNorm B) (hBc : B.Connected) (hcut : PrefixCut B p hpe)
    (M : ℕ) (hM : ∀ i : Fin n, p ≤ i.val → B.row i.succ < M) (j : Fin n) (hj : p ≤ j.val) :
    coframeVecOf cohLetters B j ∈ letterField M := by
  classical
  set T := properMatrixOf cohLetters B with hT
  set Tl := T.toSquareBlock (cutGrade p) 1 with hTl
  have hdet := det_lower_ne_zero B hpe hBc hcut
  set g := coframeVecOf cohLetters B with hg
  have hsol : T *ᵥ g = -topVecOf cohLetters B := properMatrix_mulVec_coframeVecOf _ _ (by
    exact properDet_cohLetters_ne_zero hBc)
  have h0 : ∀ i j : Fin n, p ≤ i.val → j.val < p → T i j = 0 := fun i j hi hj =>
    properMatrix_lowerLeft B hpe hcut i j hi hj
  -- the lower system
  let gl : {a : Fin n // cutGrade p a = 1} → CohField := fun a => g a.1
  let fl : {a : Fin n // cutGrade p a = 1} → CohField := fun a => -topVecOf cohLetters B a.1
  have hgrade : ∀ a : Fin n, cutGrade p a = 1 ↔ p ≤ a.val := fun a => by
    unfold cutGrade; split_ifs with h <;> simp <;> omega
  have hlow : Tl *ᵥ gl = fl := by
    funext a
    have hrow := congrFun hsol a.1
    have hap : p ≤ a.1.val := (hgrade a.1).mp a.2
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at hrow
    simp only [Matrix.mulVec, dotProduct, hTl, Matrix.toSquareBlock_def, Matrix.submatrix_apply,
      gl, fl, Pi.neg_apply, Matrix.of_apply]
    rw [← hrow, ← Finset.sum_subtype (Finset.univ.filter fun x : Fin n => cutGrade p x = 1)
      (fun x => by simp) (fun x => T a.1 x * g x)]
    refine Finset.sum_filter_of_ne fun x _ hne => ?_
    by_contra hx
    have hxp : x.val < p := by
      by_contra h'; exact hx ((hgrade x).mpr (by omega))
    exact hne (by rw [h0 a.1 x hap hxp, zero_mul])
  have hgl : gl = Tl⁻¹ *ᵥ fl := by
    rw [← hlow, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  set F := letterField M with hF
  have hTl_mem : ∀ a b, Tl a b ∈ F := by
    intro a b
    have hap : p ≤ a.1.val := (hgrade a.1).mp a.2
    have hcpos : 0 < B.col b.1.castSucc := by
      have := col_pos_of_ne_last B hB b.1.castSucc (Fin.castSucc_lt_last b.1).ne
      exact this
    simp only [hTl, Matrix.toSquareBlock_def, Matrix.submatrix_apply, hT, properMatrixOf,
      Matrix.of_apply]
    exact letterOf_mem_letterField (by have := hM a.1 hap; omega)
  have hfl_mem : ∀ a, fl a ∈ F := by
    intro a
    have hap : p ≤ a.1.val := (hgrade a.1).mp a.2
    have h0' : B.col (Fin.last n) = 0 := hB
    simp only [fl, topVecOf, Pi.neg_apply]
    refine F.neg_mem (letterOf_mem_letterField ?_)
    have := hM a.1 hap
    omega
  have hjmem : (⟨j, (hgrade j).mpr hj⟩ : {a : Fin n // cutGrade p a = 1}) = ⟨j, (hgrade j).mpr hj⟩ := rfl
  have := congrFun hgl ⟨j, (hgrade j).mpr hj⟩
  simp only [gl] at this
  rw [this]
  simp only [Matrix.mulVec, dotProduct]
  exact Subfield.sum_mem _ fun k _ => F.mul_mem (inv_entry_mem_subfield' F Tl hTl_mem _ _)
    (hfl_mem k)


include hpe in
/-- **The numerator coefficients are lower.**  For a position `b` below `M` and below every
prefix column, the numerator coefficient `P_b = [HG]_b` lies in `letterField M`, where `M`
exceeds every lower row. -/
theorem numerator_coeff_mem_lower (hB : IsNorm B) (hBc : B.Connected) (hcut : PrefixCut B p hpe)
    (M : ℕ) (hM : ∀ i : Fin n, p ≤ i.val → B.row i.succ < M) (b : ℕ) (hbM : (b : ℤ) < M)
    (hb : ∀ j : Fin n, j.val < p → (b : ℤ) < B.col j.castSucc) :
    PowerSeries.coeff b (letterSeries * (coframe B : PowerSeries CohField)) ∈ letterField M := by
  have h0 : B.col (Fin.last n) = 0 := hB
  have := coeff_coframe_vac cohLetters B hB b
  change PowerSeries.coeff b (PowerSeries.mk cohLetters *
    (coframeOf cohLetters B : PowerSeries CohField)) ∈ _
  rw [this, h0, sub_zero]
  refine Subfield.add_mem _ (letterOf_mem_letterField hbM) ?_
  unfold dotProduct
  refine Subfield.sum_mem _ fun j _ => ?_
  by_cases hj : j.val < p
  · have : letterOf cohLetters ((b : ℤ) - B.col j.castSucc) = 0 := by
      unfold letterOf; rw [if_pos (by have := hb j hj; omega)]
    show letterOf cohLetters ((b : ℤ) - B.col j.castSucc) * _ ∈ _
    rw [this, zero_mul]; exact Subfield.zero_mem _
  · refine Subfield.mul_mem _ (letterOf_mem_letterField ?_)
      (lower_coframe_mem B hpe hB hBc hcut M hM j (by omega))
    have := col_pos_of_ne_last B hB j.castSucc (Fin.castSucc_lt_last j).ne
    omega

end Lower

end SkewCoframeRigidity.UnitRestoration
