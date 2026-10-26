/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Connected.Algebra
import SkewCoframeRigidity.Unshifted.Components
import SkewCoframeRigidity.Unshifted.Endpoints

/-!
# The child of a connected proper corner

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`), the connected corner: the proper corner of `V`, translated by `-1`, is
an actual diagram `E` of span `M - 2`, and the endpoint column is `a = -z g / k` with `g` the own
coframe of `E` and `k` its top quotient.  Sorry-free.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {k : ℕ}

/-- The proper corner of `V` translated by `-1`, a diagram of `k + 1` rows. -/
def cornerChild (V : BetaDiagram (k + 1 + 1))
    (hnu : ∀ i : Fin (k + 1), V.col i.castSucc < V.row i.succ) : BetaDiagram (k + 1) where
  row i := V.row i.succ - 1
  col j := V.col j.castSucc - 1
  row_strictAnti := fun i j hij => by
    have := V.row_strictAnti (Fin.succ_lt_succ_iff.2 hij)
    change V.row j.succ - 1 < V.row i.succ - 1
    omega
  col_strictAnti := fun i j hij => by
    have := V.col_strictAnti (Fin.castSucc_lt_castSucc_iff.2 hij)
    change V.col j.castSucc - 1 < V.col i.castSucc - 1
    omega
  row_nonempty := fun i => by
    have := hnu i
    change V.col i.castSucc - 1 < V.row i.succ - 1
    omega

section Port

variable {K : Type*} [Field K] (V : BetaDiagram (k + 1 + 1))
  (hnu : ∀ i : Fin (k + 1), V.col i.castSucc < V.row i.succ)
  (hVn : V.col (Fin.last (k + 1)) = 0) (hcol1 : V.col (Fin.last k).castSucc = 1)
  (hport : V.row 1 + 1 = V.row 0)

theorem fullMatrixOf_cornerChild (h : ℕ → K) :
    fullMatrixOf h (cornerChild V hnu) = properMatrixOf h V := by
  ext p q
  simp only [fullMatrixOf, properMatrixOf, Matrix.of_apply, cornerChild]
  congr 1
  ring

include hVn hcol1 hport in
theorem span_cornerChild : span (cornerChild V hnu) + 2 = span V := by
  have h1 := span_cast V
  have h2 := span_cast (cornerChild V hnu)
  have e : (cornerChild V hnu).largestLabel =
      V.row 1 - 1 - (V.col (Fin.last k).castSucc - 1) := rfl
  have e1 : V.largestLabel = V.row 0 - V.col (Fin.last (k + 1)) := rfl
  omega

include hVn hcol1 hport in
/-- The endpoint column of a connected corner: `a k = -z g`. -/
theorem corner_port (h : ℕ → K) (hT : (properMatrixOf h V).det ≠ 0)
    (hTE : (properMatrixOf h (cornerChild V hnu)).det ≠ 0) :
    topQuotientOf h (cornerChild V hnu) ≠ 0 ∧
      endpointA h V * C (topQuotientOf h (cornerChild V hnu)) =
        -(X ^ 1 * coframeOf h (cornerChild V hnu)) := by
  refine endpointA_block h V hT (cornerChild V hnu) 1 id id Function.injective_id ?_ ?_ ?_ ?_ ?_
    hTE ?_
  · intro p
    have := rowPos_cast V p
    simp only [cornerChild, id]
    omega
  · intro q
    have := colPos_cast V q
    simp only [cornerChild, id]
    omega
  · simp only [cornerChild]
    omega
  · intro i hi
    exact absurd ⟨i, rfl⟩ hi
  · have h1 := rowPos_cast V 0
    have h2 := span_cast V
    unfold BetaDiagram.largestLabel at h2
    simp only [id, Fin.succ_zero_eq_one] at h1 ⊢
    omega
  · rw [fullMatrixOf_cornerChild]; exact hT

end Port

section Rotation

variable (V : BetaDiagram (k + 1 + 1))
  (hnu : ∀ i : Fin (k + 1), V.col i.castSucc < V.row i.succ)
  (hVn : V.col (Fin.last (k + 1)) = 0) (hcol1 : V.col (Fin.last k).castSucc = 1)
  (hport : V.row 1 + 1 = V.row 0)

theorem rev_one : (1 : Fin (k + 1 + 1)).rev = (Fin.last k).castSucc := by
  ext; simp [Fin.val_rev]

theorem rev_castSucc_succ (i : Fin (k + 1)) : i.castSucc.rev = i.rev.succ := by
  have := i.isLt
  ext; simp [Fin.val_rev]; omega

theorem rev_succ_castSucc (i : Fin (k + 1)) : i.succ.rev = i.rev.castSucc := by
  ext; simp [Fin.val_rev]

include hnu in
theorem rotation_nu :
    ∀ i : Fin (k + 1), V.rotation.col i.castSucc < V.rotation.row i.succ := fun i => by
  have := hnu i.rev
  simp only [BetaDiagram.rotation_col, BetaDiagram.rotation_row, rev_castSucc_succ,
    rev_succ_castSucc]
  omega

include hVn hcol1 in
theorem rotation_port : V.rotation.row 1 + 1 = V.rotation.row 0 := by
  simp only [BetaDiagram.rotation_row, Fin.rev_zero, rev_one, hVn, hcol1]
  ring

include hVn hcol1 hport in
theorem rotation_col1 : V.rotation.col (Fin.last k).castSucc = 1 := by
  simp only [BetaDiagram.rotation_col, rev_castSucc_succ, Fin.rev_last, Fin.succ_zero_eq_one]
  have e : V.largestLabel = V.row 0 - V.col (Fin.last (k + 1)) := rfl
  omega

include hnu hVn hcol1 hport in
theorem cornerChild_rotation
    (hnuW : ∀ i : Fin (k + 1), V.rotation.col i.castSucc < V.rotation.row i.succ) :
    cornerChild V.rotation hnuW = (cornerChild V hnu).rotation := by
  have hs := span_cornerChild V hnu hVn hcol1 hport
  have h1 := span_cast V
  have h2 := span_cast (cornerChild V hnu)
  have ext : ∀ A B : BetaDiagram (k + 1), A.row = B.row → A.col = B.col → A = B := by
    intro A B h1 h2
    cases A
    cases B
    simp_all
  have e0 : (cornerChild V hnu).largestLabel =
      V.row 1 - 1 - (V.col (Fin.last k).castSucc - 1) := rfl
  have e1 : V.largestLabel = V.row 0 - V.col (Fin.last (k + 1)) := rfl
  have e2 : (cornerChild V hnu).largestLabel = V.largestLabel - 2 := by omega
  refine ext _ _ (funext fun i => ?_) (funext fun j => ?_)
  · simp only [BetaDiagram.rotation_row]
    rw [e2]
    simp only [cornerChild, BetaDiagram.rotation_row, BetaDiagram.rotation_col,
      rev_succ_castSucc]
    omega
  · simp only [BetaDiagram.rotation_col]
    rw [e2]
    simp only [cornerChild, BetaDiagram.rotation_row, BetaDiagram.rotation_col,
      rev_castSucc_succ]
    omega

end Rotation

section Equation

variable {K : Type*} [Field K] (V : BetaDiagram (k + 1 + 1))
  (hnu : ∀ i : Fin (k + 1), V.col i.castSucc < V.row i.succ)
  (hVn : V.col (Fin.last (k + 1)) = 0) (hcol1 : V.col (Fin.last k).castSucc = 1)
  (hport : V.row 1 + 1 = V.row 0)

theorem det_properMatrixOf_rotation (h : ℕ → K) (D : BetaDiagram (k + 1 + 1)) :
    (properMatrixOf h D.rotation).det = (properMatrixOf h D).det := by
  rw [properMatrixOf_rotation, Matrix.det_transpose_submatrix_rev]

include hnu hVn hcol1 hport in
/-- `ph:unshifted-exclusion`, connected corner: the quadratic coefficient is `z²/k²` times the
child expression of `E` and its half-turn. -/
theorem corner_equation (p : ℕ) (h : ℕ → K)
    (hT : (properMatrixOf h V).det ≠ 0)
    (hTE : (properMatrixOf h (cornerChild V hnu)).det ≠ 0)
    (hY2 : ∀ j < 2 * span V, PowerSeries.coeff j (genY2 p h V V.rotation) = 0) :
    ∀ j < 2 * span (cornerChild V hnu) + 2,
      PowerSeries.coeff j (childExpr p (span (cornerChild V hnu)) h
        (coframeOf h (cornerChild V hnu)) (coframeOf h (cornerChild V hnu).rotation)) = 0 := by
  set E := cornerChild V hnu with hE
  have hspan : span E + 2 = span V := span_cornerChild V hnu hVn hcol1 hport
  have hnuW := rotation_nu V hnu
  have hVnW : V.rotation.col (Fin.last (k + 1)) = 0 := BetaDiagram.rotation_col_last V hVn
  have hcol1W := rotation_col1 V hVn hcol1 hport
  have hportW := rotation_port V hVn hcol1
  have hTW : (properMatrixOf h V.rotation).det ≠ 0 := by
    rw [det_properMatrixOf_rotation]; exact hT
  have hrot := cornerChild_rotation V hnu hVn hcol1 hport hnuW
  have hTEW : (properMatrixOf h (cornerChild V.rotation hnuW)).det ≠ 0 := by
    rw [hrot, properMatrixOf_rotation, Matrix.det_transpose_submatrix_rev]; exact hTE
  obtain ⟨hk, ha⟩ := corner_port V hnu hVn hcol1 hport h hT hTE
  obtain ⟨hkW, hb⟩ := corner_port V.rotation hnuW hVnW hcol1W hportW h hTW hTEW
  rw [hrot] at hkW hb
  have hkeq : topQuotientOf h E.rotation = topQuotientOf h E := by
    have s1 := schurOf_eq_cornerOf_mul_topQuotientOf h E hTE
    have hTE' : (properMatrixOf h E.rotation).det ≠ 0 := by
      rw [properMatrixOf_rotation, Matrix.det_transpose_submatrix_rev]; exact hTE
    have s2 := schurOf_eq_cornerOf_mul_topQuotientOf h E.rotation hTE'
    rw [schurOf_rotation, cornerOf_rotation] at s2
    have hc : cornerOf h E ≠ 0 := by
      unfold cornerOf
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hTE
    exact mul_left_cancel₀ hc (s2.symm.trans s1)
  set kk := topQuotientOf h E with hkk
  set s : K := -kk⁻¹ with hs
  have hsk : s * kk = -1 := by rw [hs, neg_mul, inv_mul_cancel₀ hk]
  have hCk : C kk * C kk⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hk, map_one]
  have ha' : endpointA h V = C s * X * coframeOf h E := by
    have : endpointA h V = endpointA h V * C kk * C kk⁻¹ := by
      rw [mul_assoc, hCk, mul_one]
    rw [this, ha, hs, map_neg]
    ring
  have hr : ∀ i, V.rotation.row i = (V.largestLabel : ℤ) - V.col i.rev := fun i => by simp
  have hc : ∀ i, V.rotation.col i = (V.largestLabel : ℤ) - V.row i.rev := fun i => by simp
  have hb0 : endpointB h V = endpointA h V.rotation := (endpointA_rot h hr hc hVnW).symm
  have hb' : endpointB h V = C s * X * coframeOf h E.rotation := by
    rw [hb0]
    rw [hkeq] at hb
    have : endpointA h V.rotation = endpointA h V.rotation * C kk * C kk⁻¹ := by
      rw [mul_assoc, hCk, mul_one]
    rw [this, hb, hs, map_neg]
    ring
  have hg : PowerSeries.coeff (span E) (seriesOf h * (coframeOf h E : PowerSeries K)) = kk := rfl
  have hc' : PowerSeries.coeff (span E) (seriesOf h * (coframeOf h E.rotation : PowerSeries K)) =
      kk := by
    rw [← hkeq]
    unfold topQuotientOf
    rw [span_rotation]
  intro j hj
  have h1 := hY2 (j + 2) (by omega)
  simp only [genY2, genPDiff] at h1
  rw [ha', hb', ← hspan, show span E + 2 - 1 = span E + 1 from rfl,
    passage p (span E) h _ _ kk s hsk hg hc'] at h1
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    Nat.add_sub_cancel] at h1
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd h (pow_ne_zero 2 (neg_ne_zero.2 (inv_ne_zero hk)))
  · exact h

end Equation

end SkewCoframeRigidity.Unshifted
