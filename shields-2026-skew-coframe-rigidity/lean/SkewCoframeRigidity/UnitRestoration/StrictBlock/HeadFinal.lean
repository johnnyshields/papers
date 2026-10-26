/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadDescent
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadGen
import SkewCoframeRigidity.Stationary.DerivCoframe

/-!
# The `h_t`-derivative of the coframe equations

Sorry-free groundwork for `block_survive`: the derivative of the proper system in the head
letter `h_t`, `t` the head row of the strict block.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.FixedCap Polynomial Matrix

variable {n p e : ℕ}

theorem dRaw_letterOf (t : ℕ) (z : ℤ) :
    dRaw t (letterOf cohLetters z) = if z = (t : ℤ) then 1 else 0 := by
  unfold letterOf
  split_ifs with h1 h2 h2
  · omega
  · exact dRaw_zero t
  · rw [dRaw_letter, if_pos (by omega)]
  · rw [dRaw_letter, if_neg (by omega)]

section Deriv

variable (B : BetaDiagram (n + 1)) (hB : IsNorm B) (hBc : B.Connected) (t : ℕ)

include hBc in
/-- The derivative of the proper system in `h_t`. -/
theorem dg_system (i : Fin n) :
    ∑ j, properMatrixOf cohLetters B i j * dRaw t (coframeVecOf cohLetters B j) =
      -dRaw t (topVecOf cohLetters B i) -
        ∑ j, dRaw t (properMatrixOf cohLetters B i j) * coframeVecOf cohLetters B j := by
  have hsol := properMatrix_mulVec_coframeVecOf cohLetters B (properDet_cohLetters_ne_zero hBc)
  have := congrArg (dRaw t) (congrFun hsol i)
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at this
  rw [dRaw_neg, dRaw_sum] at this
  simp only [dRaw_mul, Finset.sum_add_distrib] at this
  linear_combination this

theorem dRaw_properMatrix_entry (i j : Fin n) :
    dRaw t (properMatrixOf cohLetters B i j) =
      if B.row i.succ - B.col j.castSucc = (t : ℤ) then 1 else 0 := by
  simp only [properMatrixOf, Matrix.of_apply]
  exact dRaw_letterOf t _

include hB in
theorem dRaw_topVec_entry (i : Fin n) :
    dRaw t (topVecOf cohLetters B i) = if B.row i.succ = (t : ℤ) then 1 else 0 := by
  have h0 : B.col (Fin.last n) = 0 := hB
  simp only [topVecOf, h0, sub_zero]
  exact dRaw_letterOf t _

include hB in
/-- Below the head row nothing depends on `h_t` except the right-hand side at the pivot. -/
theorem dRaw_properMatrix_lower (hp : p < n) 
    (ht : (t : ℤ) = B.row ⟨p + 1, by omega⟩) (i j : Fin n) (hij : p ≤ i.val) :
    dRaw t (properMatrixOf cohLetters B i j) = 0 := by
  rw [dRaw_properMatrix_entry, if_neg]
  have h1 : B.row i.succ ≤ B.row ⟨p + 1, by omega⟩ :=
    B.row_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only [Fin.val_succ]; omega)
  have h2 := col_pos_of_ne_last B hB j.castSucc (Fin.castSucc_lt_last j).ne
  omega

end Deriv


section Lead

variable (B : BetaDiagram (n + 1)) (hpe : p + e + 1 ≤ n)

/-- The embedding of the leading block into the proper indices. -/
def leadEmb (a : Fin p ⊕ Fin (e + 1)) : Fin n := ⟨leadIdx p e a, leadIdx_lt hpe a⟩

theorem leadEmb_injective : Function.Injective (leadEmb (p := p) (e := e) hpe) := by
  intro a b hab
  have := congrArg Fin.val hab
  simp only [leadEmb] at this
  rcases a with i | i <;> rcases b with j | j <;> simp only [leadIdx, Sum.elim_inl, Sum.elim_inr]
    at this
  · exact congrArg Sum.inl (Fin.ext this)
  · have := i.isLt; have := j.isLt; omega
  · have := i.isLt; have := j.isLt; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem leadEmb_range (i : Fin n) :
    i.val < p + e + 1 ↔ ∃ a, leadEmb hpe a = i := by
  constructor
  · intro hi
    refine ⟨leadPhi p e ⟨i.val, hi⟩, Fin.ext ?_⟩
    simp only [leadEmb]
    exact leadIdx_phi (p := p) (e := e) ⟨i.val, hi⟩
  · rintro ⟨a, rfl⟩
    rcases a with j | j <;> simp only [leadEmb, leadIdx, Sum.elim_inl, Sum.elim_inr]
    · have := j.isLt; omega
    · have := j.isLt; omega

theorem leadMatOf_eq_submatrix {L : Type*} [CommRing L] (h : ℕ → L) :
    leadMatOf B hpe h = (properMatrixOf h B).submatrix (leadEmb hpe) (leadEmb hpe) := rfl

theorem letterOf_of_neg {L : Type*} [Zero L] (h : ℕ → L) {z : ℤ} (hz : z < 0) :
    letterOf h z = 0 := by
  unfold letterOf; rw [if_pos hz]

/-- The cut at the end of the block: the lower rows see none of the leading columns. -/
theorem properMatrix_cut_q {L : Type*} [CommRing L] (h : ℕ → L)
    (hq : ∀ hq : p + e + 1 < n, B.row ⟨p + e + 2, by omega⟩ < B.col ⟨p + e, by omega⟩)
    (i j : Fin n) (hi : p + e + 1 ≤ i.val) (hj : j.val < p + e + 1) :
    properMatrixOf h B i j = 0 := by
  have hn : p + e + 1 < n := by have := i.isLt; omega
  have h1 := hq hn
  have h2 : B.row i.succ ≤ B.row ⟨p + e + 2, by omega⟩ :=
    B.row_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only [Fin.val_succ]; omega)
  have h3 : B.col ⟨p + e, by omega⟩ ≤ B.col j.castSucc :=
    B.col_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only [Fin.val_castSucc]; omega)
  simp only [properMatrixOf, Matrix.of_apply]
  exact letterOf_of_neg h (by omega)


variable (hcut : PrefixCut B p (by omega : p + 1 ≤ n))

include hcut in
theorem leadMatOf_lowerLeft {L : Type*} [CommRing L] (h : ℕ → L) (j : Fin (e + 1)) (i : Fin p) :
    leadMatOf B hpe h (Sum.inr j) (Sum.inl i) = 0 := by
  have hp : 0 < p := by have := i.isLt; omega
  have h1 := hcut hp
  have h2 : B.row ⟨p + j.val + 1, by omega⟩ ≤ B.row ⟨p + 1, by omega⟩ :=
    B.row_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only; omega)
  have h3 : B.col ⟨p - 1, by omega⟩ ≤ B.col ⟨i.val, by omega⟩ :=
    B.col_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only; have := i.isLt; omega)
  have e1 : leadRow B hpe (Sum.inr j) = B.row ⟨p + j.val + 1, by omega⟩ := rfl
  have e2 : leadCol B hpe (Sum.inl i) = B.col ⟨i.val, by omega⟩ := rfl
  simp only [leadMatOf, Matrix.of_apply]
  exact letterOf_of_neg h (by omega)

include hcut in
theorem leadMatOf_eq_fromBlocks {L : Type*} [CommRing L] (h : ℕ → L) :
    leadMatOf B hpe h = Matrix.fromBlocks (leadMatOf B hpe h).toBlocks₁₁
      (leadMatOf B hpe h).toBlocks₁₂ 0 (leadMatOf B hpe h).toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (leadMatOf B hpe h)]
  congr 1
  exact Matrix.ext fun i j => leadMatOf_lowerLeft B hpe hcut h i j

end Lead

section Tri

variable {κ θ : Type*} [Fintype κ] [Fintype θ] [DecidableEq κ] [DecidableEq θ]
  {F : Type*} [Field F]

/-- A solution of a block-triangular system with zero lower right-hand side has zero lower part
when the lower block is invertible. -/
theorem lower_part_zero (P : Matrix κ κ F) (Bm : Matrix κ θ F) (E : Matrix θ θ F)
    (hE : E.det ≠ 0) (z : κ ⊕ θ → F) (s : κ → F)
    (hz : Matrix.fromBlocks P Bm 0 E *ᵥ z = Sum.elim s 0) (i : θ) : z (Sum.inr i) = 0 := by
  have h1 : E *ᵥ (fun j => z (Sum.inr j)) = 0 := by
    funext i
    have := congrFun hz (Sum.inr i)
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using this
  have := Matrix.eq_zero_of_mulVec_eq_zero hE h1
  exact congrFun this i

end Tri

section Numerator

variable (B : BetaDiagram (n + 1)) (hB : IsNorm B) (hBc : B.Connected) (hpe : p + e + 1 ≤ n)
  (hcut : PrefixCut B p (by omega : p + 1 ≤ n))
  (hq : ∀ hq : p + e + 1 < n, B.row ⟨p + e + 2, by omega⟩ < B.col ⟨p + e, by omega⟩)

include hB hBc hpe hcut hq in
/-- The derivative of the lower coframe coefficients: `dg = ext(-A⁻¹(e_p + s))` where `s` is the
derivative of the prefix rows, supported on the prefix. -/
theorem dg_eq_ext (t : ℕ) (ht : (t : ℤ) = B.row ⟨p + 1, by omega⟩)
    (hA : (leadMatOf B hpe cohLetters).det ≠ 0) :
    (fun j => dRaw t (coframeVecOf cohLetters B j)) =
      extZero (leadEmb hpe)
        ((leadMatOf B hpe cohLetters)⁻¹ *ᵥ
          (-(Pi.single pivot 1 : Fin p ⊕ Fin (e + 1) → CohField) -
            Sum.elim (fun i => ∑ j, dRaw t (properMatrixOf cohLetters B (leadEmb hpe (Sum.inl i)) j) *
              coframeVecOf cohLetters B j) 0)) := by
  classical
  have hT := properDet_cohLetters_ne_zero hBc
  have hsys := dg_system B hBc t
  set T := properMatrixOf cohLetters B with hTdef
  set dg : Fin n → CohField := fun j => dRaw t (coframeVecOf cohLetters B j) with hdg
  set rhs : Fin n → CohField := fun i => -dRaw t (topVecOf cohLetters B i) -
    ∑ j, dRaw t (T i j) * coframeVecOf cohLetters B j with hrhs
  have hTdg : T *ᵥ dg = rhs := by
    funext i; exact hsys i
  have hrhs0 : ∀ i : Fin n, p + e + 1 ≤ i.val → rhs i = 0 := by
    intro i hi
    simp only [hrhs]
    rw [dRaw_topVec_entry B hB t i, if_neg, Finset.sum_eq_zero]
    · ring
    · intro j _
      rw [dRaw_properMatrix_lower B hB t (by omega) ht i j (by omega), zero_mul]
    · intro hrow
      have : B.row i.succ = B.row ⟨p + 1, by omega⟩ := by rw [← ht]; exact hrow
      have := B.row_strictAnti.injective this
      have := congrArg Fin.val this
      simp only [Fin.val_succ] at this
      omega
  have hext := inv_mulVec_eq_extZero (leadEmb_injective hpe) (leadEmb_range hpe) T hT
    (by rw [← leadMatOf_eq_submatrix]; exact hA) (fun i j hi hj => properMatrix_cut_q B cohLetters hq i j hi hj)
    rhs hrhs0
  have hdgeq : dg = T⁻¹ *ᵥ rhs := by
    rw [← hTdg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hT),
      Matrix.one_mulVec]
  rw [hdgeq, hext]
  congr 2
  funext a
  have hrow : ∀ i' : Fin n, B.row i'.succ = (t : ℤ) → i'.val = p := by
    intro i' h'
    have h1 : B.row i'.succ = B.row ⟨p + 1, by omega⟩ := by rw [← ht]; exact h'
    have h2 := congrArg Fin.val (B.row_strictAnti.injective h1)
    simp only [Fin.val_succ] at h2
    omega
  have hTz : ∀ (i' j : Fin n), p ≤ i'.val → dRaw t (T i' j) = 0 := fun i' j hi' =>
    dRaw_properMatrix_lower B hB t (by omega) ht i' j hi'
  rcases a with i | i
  · have hne : ¬ B.row (leadEmb hpe (Sum.inl i)).succ = (t : ℤ) := by
      intro h'
      have := hrow _ h'
      simp only [leadEmb, leadIdx, Sum.elim_inl] at this
      have := i.isLt; omega
    simp only [hrhs, Pi.sub_apply, Pi.neg_apply, Sum.elim_inl]
    rw [dRaw_topVec_entry B hB t, if_neg hne, Pi.single_apply, if_neg (by simp [pivot])]
    try simp
  · have hsum : ∑ j, dRaw t (T (leadEmb hpe (Sum.inr i)) j) * coframeVecOf cohLetters B j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [hTz _ j (by simp [leadEmb, leadIdx]), zero_mul]
    simp only [hrhs, Pi.sub_apply, Pi.neg_apply, Sum.elim_inr]
    rw [hsum, dRaw_topVec_entry B hB t, Pi.single_apply]
    by_cases hi : i = 0
    · subst hi
      have : B.row (leadEmb hpe (Sum.inr 0)).succ = (t : ℤ) := by
        rw [ht]; simp [leadEmb, leadIdx]
      rw [if_pos this, if_pos (by simp [pivot])]
      try simp
    · have hne : ¬ B.row (leadEmb hpe (Sum.inr i)).succ = (t : ℤ) := by
        intro h'
        have := hrow _ h'
        simp only [leadEmb, leadIdx, Sum.elim_inr] at this
        exact hi (Fin.ext (by simpa using (by omega : i.val = 0)))
      rw [if_neg hne, if_neg (by simp [pivot, hi])]
      try simp


include hcut in
theorem det_lower_block_ne_zero (hA : (leadMatOf B hpe cohLetters).det ≠ 0) :
    (leadMatOf B hpe cohLetters).toBlocks₂₂.det ≠ 0 := by
  have h := leadMatOf_eq_fromBlocks B hpe hcut cohLetters
  intro h0
  apply hA
  rw [h, Matrix.det_fromBlocks_zero₂₁, h0, mul_zero]

include hB hBc hcut hq in
/-- **The derivative of the numerator coefficient.**  For a position `b` below the head row `t`
and below every prefix column, `∂_t P_b = - w_b ⬝ A⁻¹ e_pivot`. -/
theorem dP_formula (t : ℕ) (ht : (t : ℤ) = B.row ⟨p + 1, by omega⟩)
    (hA : (leadMatOf B hpe cohLetters).det ≠ 0) (b : ℕ) (hbt : (b : ℤ) < t)
    (hbp : ∀ j : Fin n, j.val < p → (b : ℤ) < B.col j.castSucc) :
    dRaw t (PowerSeries.coeff b (letterSeries * (coframe B : PowerSeries CohField))) =
      -(wOf B hpe cohLetters (b : ℤ) ⬝ᵥ
        ((leadMatOf B hpe cohLetters)⁻¹ *ᵥ Pi.single pivot 1)) := by
  classical
  set A := leadMatOf B hpe cohLetters with hAdef
  have h0 : B.col (Fin.last n) = 0 := hB
  have hcoef := coeff_coframe_vac cohLetters B hB b
  have hser : (letterSeries * (coframe B : PowerSeries CohField)) =
      PowerSeries.mk cohLetters * (coframeOf cohLetters B : PowerSeries CohField) := rfl
  rw [hser, hcoef, h0, sub_zero, dRaw_add, dRaw_letterOf, if_neg (by omega), zero_add]
  simp only [dotProduct]
  rw [dRaw_sum]
  have hterm : ∀ j : Fin n, dRaw t (letterOf cohLetters ((b : ℤ) - B.col j.castSucc) *
      coframeVecOf cohLetters B j) =
      letterOf cohLetters ((b : ℤ) - B.col j.castSucc) * dRaw t (coframeVecOf cohLetters B j) := by
    intro j
    rw [dRaw_mul, dRaw_letterOf, if_neg, zero_mul, zero_add]
    have := col_nonneg B hB j.castSucc
    omega
  simp only [hterm]
  have hdg := dg_eq_ext B hB hBc hpe hcut hq t ht hA
  have hdg' := fun j => congrFun hdg j
  simp only [hdg']
  rw [sum_extZero (leadEmb_injective hpe)]
  -- identify the sum with the lead dot product
  set s' : Fin p ⊕ Fin (e + 1) → CohField := Sum.elim (fun i => ∑ j, dRaw t (properMatrixOf cohLetters B
    (leadEmb hpe (Sum.inl i)) j) * coframeVecOf cohLetters B j) 0 with hs'
  have hz : A⁻¹ *ᵥ (-(Pi.single pivot 1 : Fin p ⊕ Fin (e + 1) → CohField) - s') =
      -(A⁻¹ *ᵥ Pi.single pivot 1) - A⁻¹ *ᵥ s' := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_neg]
  have hAinv : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hy : A *ᵥ (A⁻¹ *ᵥ s') = s' := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAinv, Matrix.one_mulVec]
  have hfb := leadMatOf_eq_fromBlocks B hpe hcut cohLetters
  have hlow : ∀ i, (A⁻¹ *ᵥ s') (Sum.inr i) = 0 := by
    refine lower_part_zero (A.toBlocks₁₁) (A.toBlocks₁₂) _ (det_lower_block_ne_zero B hpe hcut hA) _
      (fun i => ∑ j, dRaw t (properMatrixOf cohLetters B (leadEmb hpe (Sum.inl i)) j) *
        coframeVecOf cohLetters B j) ?_
    rw [← hfb]
    exact hy
  have hw : ∀ i : Fin p, wOf B hpe cohLetters (b : ℤ) (Sum.inl i) = 0 := by
    intro i
    simp only [wOf]
    exact letterOf_of_neg _ (by
      have := hbp ⟨i.val, by have := i.isLt; omega⟩ i.isLt
      simp only [leadCol, leadIdx, Sum.elim_inl]
      exact sub_neg.mpr this)
  rw [hz]
  simp only [Fintype.sum_sum_type, Pi.sub_apply, Pi.neg_apply, hlow, hw, zero_mul, mul_zero,
    Finset.sum_const_zero, zero_add, mul_sub, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
  have hw1 : ∀ i : Fin p, letterOf cohLetters
      ((b : ℤ) - B.col (leadEmb hpe (Sum.inl i)).castSucc) = 0 := fun i => hw i
  simp only [hw1, zero_mul, Finset.sum_const_zero, zero_add, add_zero, sub_zero]
  rfl


include hB hBc hq in
/-- **The pulse correction.**  For a position `b` below every row of the lower suffix,
`h_{m-b} - ∑_s (T⁻¹ v_b)_s h_{m-S_s} = h_{X_0-b} - τ ⬝ A⁻¹ v_b`. -/
theorem pulse_factor (hA : (leadMatOf B hpe cohLetters).det ≠ 0) (b : ℕ)
    (hb : ∀ i : Fin n, p + e + 1 ≤ i.val → B.row i.succ < (b : ℤ)) :
    letterOf cohLetters ((span B : ℤ) - b) -
        ∑ s, ((properMat cohLetters (rowPos B) (colPos B))⁻¹ *ᵥ
          vacancyVec cohLetters (rowPos B) b) s * letterOf cohLetters ((span B : ℤ) - colPos B s) =
      letterOf cohLetters (B.row 0 - b) -
        topRowOf B hpe cohLetters ⬝ᵥ ((leadMatOf B hpe cohLetters)⁻¹ *ᵥ vOf B hpe cohLetters b) := by
  classical
  have h0 : B.col (Fin.last n) = 0 := hB
  have hT := properDet_cohLetters_ne_zero hBc
  have hspan : (span B : ℤ) = B.row 0 := by
    have := span_cast B
    unfold BetaDiagram.largestLabel at this
    rw [h0, sub_zero] at this
    exact this
  rw [properMat_eq, vacancyVec_eq cohLetters B hB]
  set T := properMatrixOf cohLetters B with hTdef
  have hext := inv_mulVec_eq_extZero (leadEmb_injective hpe) (leadEmb_range hpe) T hT
    (by rw [← leadMatOf_eq_submatrix]; exact hA)
    (fun i j hi hj => properMatrix_cut_q B cohLetters hq i j hi hj)
    (fun i => letterOf cohLetters (B.row i.succ - b))
    (fun i hi => letterOf_of_neg _ (by have := hb i hi; omega))
  rw [hext, hspan]
  have hsum := sum_extZero (leadEmb_injective hpe)
    ((T.submatrix (leadEmb hpe) (leadEmb hpe))⁻¹ *ᵥ fun a => letterOf cohLetters
      (B.row (leadEmb hpe a).succ - b))
    (fun s => letterOf cohLetters (B.row 0 - (colPos B s : ℤ)))
  have hcol : ∀ s, (colPos B s : ℤ) = B.col s.castSucc := fun s => by
    have := colPos_cast B s; rw [h0, sub_zero] at this; exact this
  have e1 : ∑ s, ((extZero (leadEmb hpe) ((T.submatrix (leadEmb hpe) (leadEmb hpe))⁻¹ *ᵥ
        fun a => letterOf cohLetters (B.row (leadEmb hpe a).succ - b))) s) *
        letterOf cohLetters (B.row 0 - (colPos B s : ℤ)) =
      topRowOf B hpe cohLetters ⬝ᵥ ((leadMatOf B hpe cohLetters)⁻¹ *ᵥ vOf B hpe cohLetters b) := by
    rw [show (∑ s, (extZero (leadEmb hpe) _ s) * letterOf cohLetters (B.row 0 - (colPos B s : ℤ))) =
      ∑ s, letterOf cohLetters (B.row 0 - (colPos B s : ℤ)) * (extZero (leadEmb hpe) _ s) from
        Finset.sum_congr rfl fun s _ => mul_comm _ _, hsum]
    simp only [dotProduct, topRowOf, vOf, leadMatOf_eq_submatrix, leadEmb, hcol]
    refine Finset.sum_congr rfl fun a _ => ?_
    rfl
  simp only [hcol] at e1 ⊢
  rw [e1]

end Numerator

end SkewCoframeRigidity.UnitRestoration
