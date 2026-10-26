/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadData
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadColumn
import Mathlib.GroupTheory.Perm.Fin

/-!
# The strict-block identity on actual boards

Specializes `strict_block_identity_poly` to the leading `(p + e + 1)`-square block of the proper
matrix of a connected zero-free board `B`, with prefix `P` of `p` indices and block `E` of
`e + 1` indices (`HeadData.lean`).  The block form of the leading matrix, the identifications
of `s_E`, `s_N`, `ṡ_E^{(x)}` and `ṡ_N^{(x)}` with the determinants and adjugate forms of the
split and row-replaced matrices, and the resulting identity for one restored position `x`
between the least column and the head row of `E`.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity Matrix

variable {n p e : ℕ}

section Leading

variable (B : BetaDiagram (n + 1)) (hpe : p + e + 1 ≤ n)

/-- The proper index of an entry of the leading block: prefix indices `i`, then block indices
`p + j`. -/
def leadIdx (p e : ℕ) : Fin p ⊕ Fin (e + 1) → ℕ := Sum.elim (fun i => i.val) fun j => p + j.val

theorem leadIdx_lt (hpe : p + e + 1 ≤ n) (a : Fin p ⊕ Fin (e + 1)) : leadIdx p e a < n := by
  rcases a with i | j
  · have := i.isLt; simp only [leadIdx, Sum.elim_inl]; omega
  · have := j.isLt; simp only [leadIdx, Sum.elim_inr]; omega

/-- The row beta of the proper row of an entry of the leading block. -/
def leadRow (a : Fin p ⊕ Fin (e + 1)) : ℤ :=
  B.row ⟨leadIdx p e a + 1, by have := leadIdx_lt hpe a; omega⟩

/-- The column beta of the native column of an entry of the leading block. -/
def leadCol (a : Fin p ⊕ Fin (e + 1)) : ℤ :=
  B.col ⟨leadIdx p e a, by have := leadIdx_lt hpe a; omega⟩

/-- The leading `(p + e + 1)`-square block of the proper matrix, split into prefix and block. -/
noncomputable def leadMat : Matrix (Fin p ⊕ Fin (e + 1)) (Fin p ⊕ Fin (e + 1)) CompleteRing :=
  Matrix.of fun a b => complete (leadRow B hpe a - leadCol B hpe b)

end Leading


section Blocks

variable (B : BetaDiagram (n + 1)) (hpe : p + e + 1 ≤ n) (hz : ZeroFree B) (hB : B.Connected)

/-- The prefix `P` as an actual diagram of `p` rows. -/
def prefixBoard : BetaDiagram p where
  row i := B.row ⟨i.val + 1, by have := i.isLt; omega⟩
  col i := B.col ⟨i.val, by have := i.isLt; omega⟩
  row_strictAnti := by
    intro i j hij
    exact B.row_strictAnti (show (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)) <
      ⟨j.val + 1, by have := j.isLt; omega⟩ from by rw [Fin.lt_def]; simp only; omega)
  col_strictAnti := by
    intro i j hij
    exact B.col_strictAnti (show (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1)) <
      ⟨j.val, by have := j.isLt; omega⟩ from by rw [Fin.lt_def]; simp only; omega)
  row_nonempty := by
    intro i
    have h1 : B.col ⟨i.val, by have := i.isLt; omega⟩ ≤
        B.row ⟨i.val + 1, by have := i.isLt; omega⟩ :=
      hB.2 ⟨i.val, by have := i.isLt; omega⟩ (by simp only; have := i.isLt; omega)
    have h2 := hz ⟨i.val + 1, by have := i.isLt; omega⟩ ⟨i.val, by have := i.isLt; omega⟩
    show B.col _ < B.row _
    omega


variable (hcut : PrefixCut B p (by omega : p + 1 ≤ n))

include hcut in
theorem leadMat_lowerLeft (j : Fin (e + 1)) (i : Fin p) :
    leadMat B hpe (Sum.inr j) (Sum.inl i) = 0 := by
  have hp : 0 < p := by have := i.isLt; omega
  have h1 := hcut hp
  have h2 : B.row ⟨p + j.val + 1, by omega⟩ ≤ B.row ⟨p + 1, by omega⟩ :=
    B.row_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only; omega)
  have h3 : B.col ⟨p - 1, by omega⟩ ≤ B.col ⟨i.val, by omega⟩ :=
    B.col_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only; have := i.isLt; omega)
  change complete (leadRow B hpe (Sum.inr j) - leadCol B hpe (Sum.inl i)) = 0
  apply complete_of_neg
  have e1 : leadRow B hpe (Sum.inr j) = B.row ⟨p + j.val + 1, by omega⟩ := rfl
  have e2 : leadCol B hpe (Sum.inl i) = B.col ⟨i.val, by omega⟩ := rfl
  omega

include hcut in
theorem leadMat_eq_fromBlocks :
    leadMat B hpe = Matrix.fromBlocks (leadMat B hpe).toBlocks₁₁ (leadMat B hpe).toBlocks₁₂ 0
      (leadMat B hpe).toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (leadMat B hpe)]
  congr 1
  exact Matrix.ext fun i j => leadMat_lowerLeft B hpe hcut i j

theorem leadMat_toBlocks₂₂ :
    (leadMat B hpe).toBlocks₂₂ = (blockBoard B hpe hz hB).matrix := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.toBlocks₂₂, Matrix.of_apply, leadMat, BetaDiagram.matrix]
  have e1 : leadRow B hpe (Sum.inr i) = B.row ⟨p + 1 + i.val, by omega⟩ := by
    unfold leadRow leadIdx; simp only [Sum.elim_inr]; congr 2; omega
  have e2 : leadCol B hpe (Sum.inr j) = B.col ⟨p + j.val, by omega⟩ := rfl
  rw [e1, e2]
  change _ = complete ((B.row ⟨p + 1 + i.val, by omega⟩ - blockLeast B hpe) -
    (B.col ⟨p + j.val, by omega⟩ - blockLeast B hpe))
  congr 1; ring

theorem leadMat_toBlocks₁₁ :
    (leadMat B hpe).toBlocks₁₁ = (prefixBoard B hpe hz hB).matrix := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply, leadMat, BetaDiagram.matrix]
  rfl

end Blocks

section Perm

/-- The cyclic row permutation moving the pivot row `p` to the top. -/
def piPerm (p e : ℕ) : Equiv.Perm (Fin (p + e + 1)) :=
  (Fin.cycleRange ⟨p, by omega⟩).symm

theorem piPerm_val (k : Fin (p + e + 1)) :
    ((piPerm p e) k).val = if k.val = 0 then p else if k.val ≤ p then k.val - 1 else k.val := by
  have hk : Fin.cycleRange ⟨p, by omega⟩ (piPerm p e k) = k := Equiv.apply_symm_apply _ _
  set j := piPerm p e k with hj
  rw [Fin.cycleRange_apply] at hk
  have hk' := congrArg Fin.val hk
  by_cases h1 : j < (⟨p, by omega⟩ : Fin (p + e + 1))
  · rw [if_pos h1] at hk'
    have h1' : j.val < p := h1
    have hl : j < Fin.last (p + e) := by rw [Fin.lt_def]; simp only [Fin.val_last]; omega
    rw [Fin.val_add_one_of_lt hl] at hk'
    have : k.val ≠ 0 := by omega
    have : k.val ≤ p := by omega
    simp only [*, if_false, if_true]
    omega
  · by_cases h2 : j = (⟨p, by omega⟩ : Fin (p + e + 1))
    · rw [if_neg h1, if_pos h2] at hk'
      simp only [Fin.val_zero] at hk'
      have : j.val = p := by rw [h2]
      simp only [← hk', if_true]
      exact this
    · rw [if_neg h1, if_neg h2] at hk'
      have : p < j.val := by
        rw [Fin.lt_def] at h1; have := Fin.val_ne_of_ne h2; simp only at *; omega
      simp only [hk']
      have : k.val ≠ 0 := by omega
      have : ¬ k.val ≤ p := by omega
      simp only [*, if_false]

end Perm

section Numerator

variable (B : BetaDiagram (n + 1)) (hpe : p + e + 1 ≤ n) (hz : ZeroFree B) (hB : B.Connected)
  (hcut : PrefixCut B p (by omega : p + 1 ≤ n))

/-- The splitting of a flat index of the leading block into prefix and block. -/
def leadPhi (p e : ℕ) (k : Fin (p + e + 1)) : Fin p ⊕ Fin (e + 1) := finSumFinEquiv.symm k

theorem leadIdx_phi (k : Fin (p + e + 1)) : leadIdx p e (leadPhi p e k) = k.val := by
  unfold leadPhi
  by_cases h : k.val < p
  · have : k = Fin.castAdd (e + 1) ⟨k.val, h⟩ := Fin.ext rfl
    rw [this, finSumFinEquiv_symm_apply_castAdd]
    rfl
  · have hk : k.val - p < e + 1 := by have := k.isLt; omega
    have : k = Fin.natAdd p ⟨k.val - p, hk⟩ := Fin.ext (by simp only [Fin.val_natAdd]; omega)
    rw [this, finSumFinEquiv_symm_apply_natAdd]
    simp only [leadIdx, Sum.elim_inr, Fin.val_natAdd]

theorem leadRow_phi (k : Fin (p + e + 1)) :
    leadRow B hpe (leadPhi p e k) = B.row ⟨k.val + 1, by have := k.isLt; omega⟩ := by
  unfold leadRow
  have := leadIdx_phi (p := p) (e := e) k
  congr 2
  omega

theorem leadCol_phi (k : Fin (p + e + 1)) :
    leadCol B hpe (leadPhi p e k) = B.col ⟨k.val, by have := k.isLt; omega⟩ := by
  unfold leadCol
  have := leadIdx_phi (p := p) (e := e) k
  congr 2

/-- The top row `τ_a = h_{X_0 - Y_a}` of the numerator matrix. -/
noncomputable def topRowVec : Fin p ⊕ Fin (e + 1) → CompleteRing :=
  fun a => complete (B.row 0 - leadCol B hpe a)

/-- The pivot of the block: the head row of `E`. -/
def pivot : Fin p ⊕ Fin (e + 1) := Sum.inr 0

theorem leadPhi_p (hp : p < p + e + 1) : leadPhi p e ⟨p, hp⟩ = pivot := by
  unfold leadPhi pivot
  have : (⟨p, hp⟩ : Fin (p + e + 1)) = Fin.natAdd p (0 : Fin (e + 1)) := Fin.ext (by simp)
  rw [this, finSumFinEquiv_symm_apply_natAdd]

/-- `N` is the leading block with its pivot row replaced by the top row, rows permuted cyclically
so that the top row comes first. -/
theorem numeratorBoard_matrix :
    (numeratorBoard B hpe hz hB hcut).matrix =
      ((leadMat B hpe).updateRow pivot (topRowVec B hpe)).submatrix
        (fun k => leadPhi p e (piPerm p e k)) (leadPhi p e) := by
  refine Matrix.ext fun k l => ?_
  have hcol : (numeratorBoard B hpe hz hB hcut).col l =
      B.col ⟨l.val, by have := l.isLt; omega⟩ - blockLeast B hpe := numeratorBoard_col B hpe hz hB hcut l
  have hrow := numeratorBoard_row B hpe hz hB hcut k
  simp only [Matrix.submatrix_apply, BetaDiagram.matrix, Matrix.of_apply]
  rw [hcol]
  have hpv := piPerm_val (p := p) (e := e) k
  by_cases hk0 : k.val = 0
  · have hk : k = 0 := Fin.ext hk0
    have hp : piPerm p e k = ⟨p, by omega⟩ := Fin.ext (by rw [hpv]; simp [hk0])
    rw [hp, leadPhi_p _, Matrix.updateRow_self]
    show complete _ = complete (B.row 0 - leadCol B hpe (leadPhi p e l))
    rw [leadCol_phi B hpe l, hrow]
    simp only [hk0, if_true, Nat.zero_lt_succ]
    congr 1
    have h0 : B.row ⟨0, by omega⟩ = B.row 0 := rfl
    rw [h0]; ring
  · have hne : leadPhi p e (piPerm p e k) ≠ pivot := by
      intro h
      have h1 := congrArg (leadIdx p e) h
      rw [leadIdx_phi] at h1
      simp only [pivot, leadIdx, Sum.elim_inr, Fin.val_zero, add_zero] at h1
      rw [hpv] at h1
      by_cases hk1 : k.val ≤ p
      · simp only [hk0, hk1, ite_false, ite_true] at h1; omega
      · simp only [hk0, hk1, ite_false] at h1; omega
    rw [Matrix.updateRow_ne hne]
    show complete _ = complete (leadRow B hpe (leadPhi p e (piPerm p e k)) - leadCol B hpe (leadPhi p e l))
    rw [leadCol_phi B hpe l, leadRow_phi B hpe, hrow]
    congr 1
    by_cases hk1 : k.val ≤ p
    · have h2 : k.val < p + 1 := by omega
      simp only [h2, ite_true]
      have : B.row ⟨k.val, by omega⟩ = B.row ⟨(piPerm p e k).val + 1, by omega⟩ := by
        congr 2; rw [hpv]; simp only [hk0, hk1, ite_false, ite_true]; omega
      rw [this]; ring
    · have h2 : ¬ k.val < p + 1 := by omega
      simp only [h2, ite_false]
      have : B.row ⟨k.val + 1, by omega⟩ = B.row ⟨(piPerm p e k).val + 1, by omega⟩ := by
        congr 2; rw [hpv]; simp only [hk0, hk1, ite_false]
      rw [this]; ring


/-- The replaced matrix `S`: the leading block with the pivot row replaced by the top row. -/
noncomputable def replMat : Matrix (Fin p ⊕ Fin (e + 1)) (Fin p ⊕ Fin (e + 1)) CompleteRing :=
  (leadMat B hpe).updateRow pivot (topRowVec B hpe)

theorem sign_piPerm : (Equiv.Perm.sign (piPerm p e) : ℤˣ) = (-1) ^ p := by
  unfold piPerm
  rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange]

/-- `s_N = (-1)^p det S`. -/
theorem numeratorBoard_schur :
    (numeratorBoard B hpe hz hB hcut).schur = (-1) ^ p * (replMat B hpe).det := by
  unfold BetaDiagram.schur
  rw [numeratorBoard_matrix]
  change (((replMat B hpe).submatrix (fun k => leadPhi p e (piPerm p e k)) (leadPhi p e))).det = _
  have h1 : ((replMat B hpe).submatrix (fun k => leadPhi p e (piPerm p e k)) (leadPhi p e)) =
      ((replMat B hpe).submatrix (leadPhi p e) (leadPhi p e)).submatrix (piPerm p e) id := by
    exact Matrix.ext fun a b => rfl
  have h2 : ((replMat B hpe).submatrix (leadPhi p e) (leadPhi p e)).det = (replMat B hpe).det :=
    Matrix.det_submatrix_equiv_self ((finSumFinEquiv (m := p) (n := e + 1)).symm : Fin (p + e + 1) ≃ _) (replMat B hpe)
  rw [h1, Matrix.det_permute, h2, sign_piPerm]
  simp


theorem numeratorBoard_row_eq (k : Fin (p + e + 1)) :
    (numeratorBoard B hpe hz hB hcut).row k + blockLeast B hpe =
      if leadPhi p e (piPerm p e k) = pivot then B.row 0
      else leadRow B hpe (leadPhi p e (piPerm p e k)) := by
  have hrow := numeratorBoard_row B hpe hz hB hcut k
  have hpv := piPerm_val (p := p) (e := e) k
  by_cases hk0 : k.val = 0
  · have hp : piPerm p e k = ⟨p, by omega⟩ := Fin.ext (by rw [hpv]; simp [hk0])
    rw [hp, leadPhi_p _, if_pos rfl, hrow]
    simp only [hk0, Nat.zero_lt_succ, ite_true]
    have h0 : B.row ⟨0, by omega⟩ = B.row 0 := rfl
    rw [h0]; ring
  · have hne : leadPhi p e (piPerm p e k) ≠ pivot := by
      intro h
      have h1 := congrArg (leadIdx p e) h
      rw [leadIdx_phi] at h1
      simp only [pivot, leadIdx, Sum.elim_inr, Fin.val_zero, add_zero] at h1
      rw [hpv] at h1
      by_cases hk1 : k.val ≤ p
      · simp only [hk0, hk1, ite_false, ite_true] at h1; omega
      · simp only [hk0, hk1, ite_false] at h1; omega
    rw [if_neg hne, leadRow_phi B hpe, hrow]
    by_cases hk1 : k.val ≤ p
    · have h2 : k.val < p + 1 := by omega
      simp only [h2, ite_true]
      have : B.row ⟨k.val, by omega⟩ = B.row ⟨(piPerm p e k).val + 1, by omega⟩ := by
        congr 2; rw [hpv]; simp only [hk0, hk1, ite_false, ite_true]; omega
      rw [this]; ring
    · have h2 : ¬ k.val < p + 1 := by omega
      simp only [h2, ite_false]
      have : B.row ⟨k.val + 1, by omega⟩ = B.row ⟨(piPerm p e k).val + 1, by omega⟩ := by
        congr 2; rw [hpv]; simp only [hk0, hk1, ite_false]
      rw [this]; ring

/-- The column `a_x = (h_{leadRow a - x})_a`, with the pivot entry replaced by `h_{X_0 - x}`. -/
noncomputable def atilVec (x : ℤ) : Fin p ⊕ Fin (e + 1) → CompleteRing :=
  Function.update (fun a => complete (leadRow B hpe a - x)) pivot (complete (B.row 0 - x))

/-- The row `w_x = (h_{x - leadCol a})_a`. -/
noncomputable def wVec (x : ℤ) : Fin p ⊕ Fin (e + 1) → CompleteRing :=
  fun a => complete (x - leadCol B hpe a)

theorem restoreCol_numerator (x' : ℤ) (k : Fin (p + e + 1)) :
    restoreCol (numeratorBoard B hpe hz hB hcut) x' k =
      atilVec B hpe (x' + blockLeast B hpe) (leadPhi p e (piPerm p e k)) := by
  have h := numeratorBoard_row_eq B hpe hz hB hcut k
  unfold restoreCol atilVec
  rw [Function.update_apply]
  by_cases hk : leadPhi p e (piPerm p e k) = pivot
  · rw [if_pos hk] at h ⊢
    congr 1; omega
  · rw [if_neg hk] at h ⊢
    congr 1; omega

theorem restoreRow_numerator (x' : ℤ) (l : Fin (p + e + 1)) :
    restoreRow (numeratorBoard B hpe hz hB hcut) x' l =
      wVec B hpe (x' + blockLeast B hpe) (leadPhi p e l) := by
  unfold restoreRow wVec
  rw [numeratorBoard_col, leadCol_phi]
  congr 1; omega


/-- `ṡ_N^{(x)} = (-1)^p · (-w_x ⬝ adj(S) ã_x)`. -/
theorem dotS_numerator (x' : ℤ) :
    dotS (numeratorBoard B hpe hz hB hcut) x' =
      (-1) ^ p * (-(wVec B hpe (x' + blockLeast B hpe) ⬝ᵥ
        ((replMat B hpe).adjugate *ᵥ atilVec B hpe (x' + blockLeast B hpe)))) := by
  set x := x' + blockLeast B hpe with hx
  set 𝔹 := bordered (replMat B hpe) (atilVec B hpe x) (wVec B hpe x) 0 with h𝔹
  let φ' : Fin (p + e + 1) ≃ Fin p ⊕ Fin (e + 1) := (finSumFinEquiv (m := p) (n := e + 1)).symm
  let Φ : Fin (p + e + 1) ⊕ Unit ≃ (Fin p ⊕ Fin (e + 1)) ⊕ Unit := Equiv.sumCongr φ' (Equiv.refl _)
  let Pp : Equiv.Perm (Fin (p + e + 1) ⊕ Unit) := Equiv.Perm.sumCongr (piPerm p e) (Equiv.refl _)
  have hbord : bordered (numeratorBoard B hpe hz hB hcut).matrix
      (restoreCol (numeratorBoard B hpe hz hB hcut) x') (restoreRow (numeratorBoard B hpe hz hB hcut) x') 0 =
      (𝔹.submatrix Φ Φ).submatrix Pp id := by
    refine Matrix.ext fun i j => ?_
    rcases i with i | u <;> rcases j with j | v
    · have := congrFun (congrFun (numeratorBoard_matrix B hpe hz hB hcut) i) j
      simpa [bordered, h𝔹, Φ, Pp, φ', replMat, leadPhi] using this
    · simpa [bordered, h𝔹, Φ, Pp, φ', leadPhi] using restoreCol_numerator B hpe hz hB hcut x' i
    · simpa [bordered, h𝔹, Φ, Pp, φ', leadPhi] using restoreRow_numerator B hpe hz hB hcut x' j
    · simp [bordered, h𝔹, Φ, Pp]
  rw [dotS_eq_det, hbord, Matrix.det_permute, Matrix.det_submatrix_equiv_self, h𝔹, det_bordered,
    zero_mul, zero_sub, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, mul_one, sign_piPerm]
  simp


/-- `ṡ_E^{(x)} = -w_E ⬝ adj(E) v_E` for the block of the leading matrix. -/
theorem dotS_block (x' : ℤ) :
    dotS (blockBoard B hpe hz hB) x' =
      -((fun j => wVec B hpe (x' + blockLeast B hpe) (Sum.inr j)) ⬝ᵥ
        ((leadMat B hpe).toBlocks₂₂.adjugate *ᵥ
          fun j => complete (leadRow B hpe (Sum.inr j) - (x' + blockLeast B hpe)))) := by
  have h1 : restoreRow (blockBoard B hpe hz hB) x' =
      fun j => wVec B hpe (x' + blockLeast B hpe) (Sum.inr j) := by
    funext j
    unfold restoreRow wVec
    change complete (x' - (B.col ⟨p + j.val, by omega⟩ - blockLeast B hpe)) = _
    congr 1
    have : leadCol B hpe (Sum.inr j) = B.col ⟨p + j.val, by omega⟩ := rfl
    rw [this]; ring
  have h2 : restoreCol (blockBoard B hpe hz hB) x' =
      fun j => complete (leadRow B hpe (Sum.inr j) - (x' + blockLeast B hpe)) := by
    funext i
    unfold restoreCol
    change complete (B.row ⟨p + 1 + i.val, by omega⟩ - blockLeast B hpe - x') = _
    congr 1
    have : leadRow B hpe (Sum.inr i) = B.row ⟨p + 1 + i.val, by omega⟩ := by
      unfold leadRow leadIdx; simp only [Sum.elim_inr]; congr 2; omega
    rw [this]; ring
  unfold dotS
  rw [h1, h2, leadMat_toBlocks₂₂ B hpe hz hB]


include hcut in
/-- The row `w_x` vanishes on the prefix columns when `x` lies below the head row. -/
theorem wVec_inl (x : ℤ) (hx : x < blockHead B hpe) (i : Fin p) :
    wVec B hpe x (Sum.inl i) = 0 := by
  have hp : 0 < p := by have := i.isLt; omega
  have h1 := hcut hp
  have h3 : B.col ⟨p - 1, by omega⟩ ≤ B.col ⟨i.val, by omega⟩ :=
    B.col_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only; have := i.isLt; omega)
  unfold wVec
  apply complete_of_neg
  have e2 : leadCol B hpe (Sum.inl i) = B.col ⟨i.val, by omega⟩ := rfl
  unfold blockHead at hx
  omega

/-- The vector `adj(T) e_pivot` of the leading matrix. -/
noncomputable def uVec : Fin p ⊕ Fin (e + 1) → CompleteRing :=
  (leadMat B hpe).adjugate *ᵥ Pi.single pivot 1

/-- **The strict-block identity on boards**, for one restored position `x = x' + a₀` between the
least column and the head row of `E`: with `D = det T`, `T` the leading block of the proper matrix,
`D (s_E ṡ_N - s_N ṡ_E) = -(-1)^p s_E (w_x ⬝ u)(h_{X_0-x} D - τ ⬝ adj(T) v_x)`. -/
theorem head_identity (x' : ℤ) (hx : x' + blockLeast B hpe < blockHead B hpe) :
    (leadMat B hpe).det *
        ((blockBoard B hpe hz hB).schur * dotS (numeratorBoard B hpe hz hB hcut) x' -
          (numeratorBoard B hpe hz hB hcut).schur * dotS (blockBoard B hpe hz hB) x') =
      -((-1) ^ p * ((blockBoard B hpe hz hB).schur *
        (wVec B hpe (x' + blockLeast B hpe) ⬝ᵥ uVec B hpe) *
        (complete (B.row 0 - (x' + blockLeast B hpe)) * (leadMat B hpe).det -
          topRowVec B hpe ⬝ᵥ ((leadMat B hpe).adjugate *ᵥ
            fun a => complete (leadRow B hpe a - (x' + blockLeast B hpe)))))) := by
  set x := x' + blockLeast B hpe with hxdef
  have hSne : (replMat B hpe).det ≠ 0 := by
    intro h
    have := numeratorBoard_schur B hpe hz hB hcut
    rw [h, mul_zero] at this
    exact (numeratorBoard B hpe hz hB hcut).schur_ne_zero this
  have hT := leadMat_eq_fromBlocks B hpe hcut
  set Pm := (leadMat B hpe).toBlocks₁₁
  set Bm := (leadMat B hpe).toBlocks₁₂
  set Em := (leadMat B hpe).toBlocks₂₂
  have hS' : ((Matrix.fromBlocks Pm Bm 0 Em).updateRow (Sum.inr (0 : Fin (e + 1)))
      (topRowVec B hpe)).det ≠ 0 := by
    rw [← hT]; exact hSne
  have key := strict_block_identity_poly Pm Bm Em (0 : Fin (e + 1)) (topRowVec B hpe)
    (fun a => complete (leadRow B hpe a - x)) (wVec B hpe x) (complete (B.row 0 - x)) hS'
    (wVec_inl B hpe hcut x hx)
  rw [← hT] at key
  have hEdet : Em.det = (blockBoard B hpe hz hB).schur := by
    have hE := leadMat_toBlocks₂₂ B hpe hz hB
    rw [show Em = (blockBoard B hpe hz hB).matrix from hE]; rfl
  have hN := numeratorBoard_schur B hpe hz hB hcut
  have hdN := dotS_numerator B hpe hz hB hcut x'
  have hdE := dotS_block B hpe hz hB x'
  rw [hN, hdN, hdE, ← hEdet]
  have hrepl : replMat B hpe = (leadMat B hpe).updateRow (Sum.inr 0) (topRowVec B hpe) := rfl
  have hatil : atilVec B hpe x = Function.update (fun a => complete (leadRow B hpe a - x))
    (Sum.inr 0) (complete (B.row 0 - x)) := rfl
  rw [hatil, hrepl]
  unfold uVec pivot
  linear_combination ((-1 : CompleteRing) ^ p) * key


/-- The surviving derivative at a restored position `x`:
`(w_x ⬝ u)(h_{X_0 - x} D - τ ⬝ adj(T) v_x)`, with `D = det T`.  Dividing by `D²` gives the
expression `(w_x ⬝ T⁻¹ e_p)(h_{X_0-x} - τ ⬝ T⁻¹ v_x)` differentiated in the head letter. -/
noncomputable def survive (x : ℤ) : CompleteRing :=
  (wVec B hpe x ⬝ᵥ uVec B hpe) *
    (complete (B.row 0 - x) * (leadMat B hpe).det -
      topRowVec B hpe ⬝ᵥ ((leadMat B hpe).adjugate *ᵥ
        fun a => complete (leadRow B hpe a - x)))

include hz hB hcut in
theorem leadMat_det_ne_zero : (leadMat B hpe).det ≠ 0 := by
  have hT := leadMat_eq_fromBlocks B hpe hcut
  rw [hT, Matrix.det_fromBlocks_zero₂₁]
  have h1 := leadMat_toBlocks₁₁ B hpe hz hB
  have h2 := leadMat_toBlocks₂₂ B hpe hz hB
  rw [h1, h2]
  exact mul_ne_zero (prefixBoard B hpe hz hB).schur_ne_zero (blockBoard B hpe hz hB).schur_ne_zero

theorem survive_eq_zero_of_lt (x : ℤ) (hx : x < blockLeast B hpe) : survive B hpe x = 0 := by
  have hw : wVec B hpe x = 0 := by
    funext a
    unfold wVec
    apply complete_of_neg
    have : blockLeast B hpe ≤ leadCol B hpe a := by
      unfold blockLeast leadCol
      exact B.col_strictAnti.antitone (by
        rw [Fin.le_iff_val_le_val]; simp only
        have := leadIdx_lt hpe a
        rcases a with i | j
        · have := i.isLt; simp only [leadIdx, Sum.elim_inl]; omega
        · have := j.isLt; simp only [leadIdx, Sum.elim_inr]; omega)
    omega
  unfold survive
  rw [hw]; simp


/-- Summing the strict-block identity over the weights: if the surviving derivative
`∑ ρ_x · survive(x)` vanishes, with `ρ` supported on genuine vacancies below the head row, then
`s_E ṡ_N = s_N ṡ_E` for the restricted weights. -/
theorem block_equation (ρ : ℤ →₀ ℚ) (hρ : ∀ x ∈ ρ.support, IsVacancy B x)
    (hρt : ∀ x ∈ ρ.support, x < blockHead B hpe)
    (hsurv : (ρ.sum fun x r => MvPolynomial.C r * survive B hpe x) = 0) :
    (blockBoard B hpe hz hB).schur *
        dotW (numeratorBoard B hpe hz hB hcut) (restrictBlock ρ (blockLeast B hpe) (blockHead B hpe)) =
      (numeratorBoard B hpe hz hB hcut).schur *
        dotW (blockBoard B hpe hz hB) (restrictBlock ρ (blockLeast B hpe) (blockHead B hpe)) := by
  classical
  set a₀ := blockLeast B hpe with ha₀
  set t := blockHead B hpe with ht
  set ρE := restrictBlock ρ a₀ t with hρE
  have hD := leadMat_det_ne_zero B hpe hz hB hcut
  -- the weighted sum over `ρE` equals the sum over `ρ`
  have hsum : (ρE.sum fun x' r => MvPolynomial.C r * survive B hpe (x' + a₀)) =
      ρ.sum fun x r => MvPolynomial.C r * survive B hpe x := by
    have h1 : (ρE.sum fun x' r => MvPolynomial.C r * survive B hpe (x' + a₀)) =
        (ρ.filter fun x => a₀ < x ∧ x < t).sum fun x r => MvPolynomial.C r * survive B hpe x := by
      rw [hρE, restrictBlock, Finsupp.sum_mapDomain_index]
      · simp
      · intro b; simp
      · intro b r₁ r₂; simp [add_mul]
    rw [h1]
    unfold Finsupp.sum
    rw [Finsupp.support_filter]
    have h2 : ∀ x ∈ ρ.support, MvPolynomial.C (ρ x) * survive B hpe x ≠ 0 → (a₀ < x ∧ x < t) := by
      intro x hx hne
      refine ⟨?_, hρt x hx⟩
      by_contra hle
      push Not at hle
      have hv := hρ x hx
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hne (by rw [survive_eq_zero_of_lt B hpe x hlt, mul_zero])
      · exact hv.2.2.2 ⟨p + e, by omega⟩ (by rw [heq]; rfl)
    have e : ∀ x ∈ ρ.support.filter (fun x => a₀ < x ∧ x < t),
        MvPolynomial.C ((Finsupp.filter (fun x => a₀ < x ∧ x < t) ρ) x) * survive B hpe x =
          MvPolynomial.C (ρ x) * survive B hpe x := by
      intro x hx
      rw [Finsupp.filter_apply_pos (fun x => a₀ < x ∧ x < t) ρ (Finset.mem_filter.mp hx).2]
    refine (Finset.sum_congr rfl e).trans (Finset.sum_filter_of_ne h2)
  -- the identity for each restored position
  have hterm : ∀ x' ∈ ρE.support,
      (leadMat B hpe).det * ((blockBoard B hpe hz hB).schur *
          dotS (numeratorBoard B hpe hz hB hcut) x' -
        (numeratorBoard B hpe hz hB hcut).schur * dotS (blockBoard B hpe hz hB) x') =
        -((-1) ^ p * (blockBoard B hpe hz hB).schur * survive B hpe (x' + a₀)) := by
    intro x' hx'
    obtain ⟨-, -, h2⟩ := mem_support_restrictBlock hx'
    have := head_identity B hpe hz hB hcut x' (by omega)
    rw [this]
    unfold survive
    ring
  have hmain : (leadMat B hpe).det *
      ((blockBoard B hpe hz hB).schur * dotW (numeratorBoard B hpe hz hB hcut) ρE -
        (numeratorBoard B hpe hz hB hcut).schur * dotW (blockBoard B hpe hz hB) ρE) = 0 := by
    unfold dotW Finsupp.sum
    have : (leadMat B hpe).det *
        ((blockBoard B hpe hz hB).schur *
            ∑ x' ∈ ρE.support, MvPolynomial.C (ρE x') *
              dotS (numeratorBoard B hpe hz hB hcut) x' -
          (numeratorBoard B hpe hz hB hcut).schur *
            ∑ x' ∈ ρE.support, MvPolynomial.C (ρE x') * dotS (blockBoard B hpe hz hB) x') =
        ∑ x' ∈ ρE.support, MvPolynomial.C (ρE x') *
          ((leadMat B hpe).det * ((blockBoard B hpe hz hB).schur *
              dotS (numeratorBoard B hpe hz hB hcut) x' -
            (numeratorBoard B hpe hz hB hcut).schur * dotS (blockBoard B hpe hz hB) x')) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x' _ => ?_
      ring
    rw [this, Finset.sum_congr rfl fun x' hx' => by rw [hterm x' hx']]
    have h3 : ∑ x' ∈ ρE.support, MvPolynomial.C (ρE x') *
        -((-1) ^ p * (blockBoard B hpe hz hB).schur * survive B hpe (x' + a₀)) =
        -((-1) ^ p * (blockBoard B hpe hz hB).schur) *
          (ρE.sum fun x' r => MvPolynomial.C r * survive B hpe (x' + a₀)) := by
      unfold Finsupp.sum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x' _ => ?_
      ring
    rw [h3, hsum, hsurv, mul_zero]
  have := (mul_eq_zero.mp hmain).resolve_left hD
  exact sub_eq_zero.mp this

end Numerator

end SkewCoframeRigidity.UnitRestoration
