/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Splice
import SkewCoframeRigidity.FixedCap.BoundaryDet
import SkewCoframeRigidity.FixedCap.CapPoly

/-!
# The splice identity

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Rigidity with the same literal cap»
(`sec:fixed-caps`, `sc:splice-identity`): for normalized `K` and `B` of spans `a` and `c`,
`s_{K ◁ B} = κ_K κ_B [z^{c+a}] H C_K G_B`, where `C_K` is the complete left coframe of `K` and
`G_B` any solution of the proper system of `B`.  The proof eliminates the top row of the splice
matrix by the left coframe vector and the last column by the right coframe, leaving a
block-triangular minor.  The identity holds for letters in any field, with `h 0` arbitrary.
Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial Matrix
open scoped Polynomial Matrix

variable {L : Type*} {k b : ℕ}

/-- The exponent `a - X_i` of the `i`-th proper row term of the left coframe of `K`. -/
def leftExp (K : BetaDiagram (k + 1)) (i : Fin k) : ℕ := (K.row 0 - K.row i.succ).toNat

/-- The top row `(H_{a - Y_j})` of the matrix of `K`, over the non-last columns. -/
def topRowOf [Zero L] (h : ℕ → L) (K : BetaDiagram (k + 1)) : Fin k → L :=
  fun j => letterOf h (K.row 0 - K.col j.castSucc)

/-- The complete left coframe vector `-(H_{a-v}) T_K⁻¹`. -/
noncomputable def leftVecOf [Field L] (h : ℕ → L) (K : BetaDiagram (k + 1)) : Fin k → L :=
  -(topRowOf h K ᵥ* (properMatrixOf h K)⁻¹)

/-- The complete left coframe `C_K(z) = 1 + ∑ c_i z^{a - X_i}`. -/
noncomputable def leftCoframeOf [Field L] (h : ℕ → L) (K : BetaDiagram (k + 1)) : L[X] :=
  capPoly (leftVecOf h K) (leftExp K)

/-- The left coframe vector solves the left proper system when `T_K` is invertible. -/
theorem leftVecOf_vecMul [Field L] (h : ℕ → L) (K : BetaDiagram (k + 1))
    (hT : IsUnit (properMatrixOf h K).det) :
    leftVecOf h K ᵥ* properMatrixOf h K = -topRowOf h K := by
  unfold leftVecOf
  rw [neg_vecMul, vecMul_vecMul, nonsing_inv_mul _ hT, vecMul_one]

section Entries

variable [Zero L] (h : ℕ → L) (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
  (hK : IsNorm K) (hB : IsNorm B)

/-- The matrix of the splice. -/
noncomputable abbrev spliceMat : Matrix (Fin (k + b + 1)) (Fin (k + b + 1)) L :=
  fullMatrixOf h (splice K B hK hB)

variable {h K B hK hB}

theorem N_tl (i j : Fin (k + b + 1)) (i' : Fin (k + 1)) (j' : Fin k)
    (hi : i.val = i'.val) (hj : j.val = j'.val) :
    spliceMat h K B hK hB i j = letterOf h (K.row i' - K.col j'.castSucc) := by
  have e1 : (⟨i.val, by omega⟩ : Fin (k + 1)) = i' := Fin.ext hi
  have e2 : (⟨j.val, by omega⟩ : Fin (k + 1)) = j'.castSucc := Fin.ext hj
  simp only [spliceMat, fullMatrixOf, Matrix.of_apply, splice]
  rw [spliceRow_top K B i (by omega), spliceCol_top K B j (by omega), e1, e2]
  congr 1
  ring

theorem N_tr (i j : Fin (k + b + 1)) (i' : Fin (k + 1)) (j' : Fin (b + 1))
    (hi : i.val = i'.val) (hj : j.val = k + j'.val) :
    spliceMat h K B hK hB i j = letterOf h (B.row 0 + K.row i' - B.col j') := by
  have e1 : (⟨i.val, by omega⟩ : Fin (k + 1)) = i' := Fin.ext hi
  have e2 : (⟨j.val - k, by omega⟩ : Fin (b + 1)) = j' := Fin.ext (by simp only; omega)
  simp only [spliceMat, fullMatrixOf, Matrix.of_apply, splice]
  rw [spliceRow_top K B i (by omega), spliceCol_bot K B j (by omega), e1, e2]

theorem N_bl (i j : Fin (k + b + 1)) (i' : Fin (b + 1)) (j' : Fin k)
    (hi : i.val = k + i'.val) (hi0 : 0 < i'.val) (hj : j.val = j'.val) :
    spliceMat h K B hK hB i j = 0 := by
  have e1 : (⟨i.val - k, by omega⟩ : Fin (b + 1)) = i' := Fin.ext (by simp only; omega)
  have e2 : (⟨j.val, by omega⟩ : Fin (k + 1)) = j'.castSucc := Fin.ext hj
  simp only [spliceMat, fullMatrixOf, Matrix.of_apply, splice]
  rw [spliceRow_bot K B i (by omega), spliceCol_top K B j (by omega), e1, e2]
  apply letterOf_neg_eq
  have h1 : B.row i' < B.row 0 := B.row_strictAnti (show (0 : Fin (b + 1)) < i' from hi0)
  have h2 := col_nonneg K hK j'.castSucc
  omega

theorem N_br (i j : Fin (k + b + 1)) (i' j' : Fin (b + 1))
    (hi : i.val = k + i'.val) (hi0 : 0 < i'.val) (hj : j.val = k + j'.val) :
    spliceMat h K B hK hB i j = letterOf h (B.row i' - B.col j') := by
  have e1 : (⟨i.val - k, by omega⟩ : Fin (b + 1)) = i' := Fin.ext (by simp only; omega)
  have e2 : (⟨j.val - k, by omega⟩ : Fin (b + 1)) = j' := Fin.ext (by simp only; omega)
  simp only [spliceMat, fullMatrixOf, Matrix.of_apply, splice]
  rw [spliceRow_bot K B i (by omega), spliceCol_bot K B j (by omega), e1, e2]

end Entries

section Sums

variable [CommRing L]

/-- A sum over `Fin (k + b + 1)` splits into the first `k + 1` indices and the last `b`. -/
theorem sum_split (f : Fin (k + b + 1) → L) :
    ∑ i, f i = ∑ i : Fin (k + 1), f ⟨i.val, by omega⟩ +
      ∑ i : Fin b, f ⟨k + 1 + i.val, by omega⟩ := by
  rw [← (finCongr (show (k + 1) + b = k + b + 1 by omega)).sum_comp f, Fin.sum_univ_add]
  rfl

/-- The weights of the row operation: `1` on the top row of `K`, `w` on its proper rows, `0`
on the rows of `B`. -/
def rowWeights (w : Fin k → L) : Fin (k + b + 1) → L := fun i =>
  if hi : i.val < k + 1 then (Fin.cons (α := fun _ => L) 1 w : Fin (k + 1) → L) ⟨i.val, hi⟩
  else 0

theorem rowWeights_zero (w : Fin k → L) : rowWeights (b := b) w 0 = 1 := by
  simp [rowWeights]

variable {h : ℕ → L} {K : BetaDiagram (k + 1)} {B : BetaDiagram (b + 1)} {hK : IsNorm K}
  {hB : IsNorm B}

/-- The combined top row, for a column in which the splice entries of the top block are
given by `f`. -/
theorem rowSum (w : Fin k → L) (x : Fin (k + b + 1)) (f : Fin (k + 1) → L)
    (hf : ∀ i : Fin (k + 1), spliceMat h K B hK hB (Fin.castLE (by omega) i) x = f i) :
    ∑ i, rowWeights w i * spliceMat h K B hK hB i x = f 0 + ∑ i : Fin k, w i * f i.succ := by
  rw [sum_split]
  have h2 : ∀ i : Fin b, rowWeights (b := b) w
      (⟨k + 1 + i.val, by have := i.isLt; omega⟩ : Fin (k + b + 1)) = 0 := by
    intro i
    unfold rowWeights
    rw [dif_neg (by simp only [not_lt]; omega)]
  simp only [h2, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_succ]
  congr 1
  · have : rowWeights (b := b) w ⟨(0 : Fin (k + 1)).val, by omega⟩ = 1 := rowWeights_zero w
    rw [this, one_mul]
    exact hf 0
  · refine Finset.sum_congr rfl fun i _ => ?_
    have : rowWeights (b := b) w ⟨(i.succ : Fin (k + 1)).val, by omega⟩ = w i := by
      simp only [rowWeights, Fin.val_succ]
      rw [dif_pos (by omega)]
      exact Fin.cons_succ (α := fun _ => L) 1 w i
    rw [this]
    exact congrArg (w i * ·) (hf i.succ)

end Sums

section Main

variable [Field L] {h : ℕ → L} {K : BetaDiagram (k + 1)} {B : BetaDiagram (b + 1)}
  {hK : IsNorm K} {hB : IsNorm B}

/-- The index `B.row 0 + K.row i - B.col y` of the top block of the splice matrix. -/
def capEntry (h : ℕ → L) (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (i : Fin (k + 1))
    (y : Fin (b + 1)) : L :=
  letterOf h (B.row 0 + K.row i - B.col y)

/-- The top row of the splice matrix after the left-coframe row operation, in the column of
`B` indexed by `y`. -/
def topCombo (h : ℕ → L) (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (w : Fin k → L)
    (y : Fin (b + 1)) : L :=
  capEntry h K B 0 y + ∑ i : Fin k, w i * capEntry h K B i.succ y

/-- The splice determinant, with the top row eliminated by `w` and the last column by `g`. -/
theorem schurOf_splice_aux (w : Fin k → L) (g : Fin b → L)
    (hw : w ᵥ* properMatrixOf h K = -topRowOf h K)
    (hg : properMatrixOf h B *ᵥ g = -topVecOf h B)
    (hKu : IsUnit (properMatrixOf h K).det) :
    schurOf h (splice K B hK hB) = cornerOf h K * cornerOf h B *
      (topCombo h K B w (Fin.last b) + ∑ j : Fin b, topCombo h K B w j.castSucc * g j) := by
  classical
  set N := spliceMat h K B hK hB with hN
  let r : Fin k → L := fun i => ∑ j : Fin b, capEntry h K B i.succ j.castSucc * g j +
    capEntry h K B i.succ (Fin.last b)
  let tl : Fin k → L := -((properMatrixOf h K)⁻¹ *ᵥ r)
  have htl : properMatrixOf h K *ᵥ tl = -r := by
    simp only [tl, mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ hKu, one_mulVec]
  let t : Fin (k + b) → L := Fin.append tl g
  let M1 := N.updateRow 0 (∑ i, rowWeights (b := b) w i • N i)
  have hdet1 : M1.det = N.det := by
    have := Matrix.det_updateRow_sum N 0 (rowWeights (b := b) w)
    rw [rowWeights_zero, one_smul] at this
    exact this
  have hM1row : ∀ (i : Fin (k + b)) x, M1 i.succ x = N i.succ x := fun i x => by
    simp only [M1]
    rw [Matrix.updateRow_ne (Fin.succ_ne_zero i)]
  have hM1top : ∀ x, M1 0 x = ∑ i, rowWeights (b := b) w i * N i x := fun x => by
    simp only [M1, Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have left0 : ∀ jl : Fin k, M1 0 (Fin.castSucc (Fin.castAdd b jl)) = 0 := by
    intro jl
    rw [hM1top, rowSum w _ (fun i => letterOf h (K.row i - K.col jl.castSucc))]
    · have := congrFun hw jl
      simp only [Matrix.vecMul, dotProduct, Pi.neg_apply, topRowOf, properMatrixOf,
        Matrix.of_apply] at this ⊢
      rw [this]
      ring
    · intro i
      exact N_tl _ _ i jl (by simp) (by simp)
  have right0 : ∀ (y : Fin (b + 1)) (x : Fin (k + b + 1)), x.val = k + y.val →
      M1 0 x = topCombo h K B w y := by
    intro y x hx
    rw [hM1top, rowSum w x (fun i => capEntry h K B i y)]
    · rfl
    · intro i
      exact N_tr _ _ i y (by simp) hx
  have hcond : ∀ i : Fin (k + b), ∑ j, M1 i.succ j.castSucc * t j + M1 i.succ (Fin.last (k + b))
      = 0 := by
    intro i
    simp only [hM1row]
    rw [Fin.sum_univ_add]
    induction i using Fin.addCases with
    | left i' =>
      have e1 : ∀ jl : Fin k, N (Fin.castAdd b i').succ (Fin.castSucc (Fin.castAdd b jl)) =
          properMatrixOf h K i' jl := fun jl =>
        N_tl _ _ i'.succ jl (by simp) (by simp)
      have e2 : ∀ jr : Fin b, N (Fin.castAdd b i').succ (Fin.castSucc (Fin.natAdd k jr)) =
          capEntry h K B i'.succ jr.castSucc := fun jr =>
        N_tr _ _ i'.succ jr.castSucc (by simp) (by simp)
      have e3 : N (Fin.castAdd b i').succ (Fin.last (k + b)) =
          capEntry h K B i'.succ (Fin.last b) :=
        N_tr _ _ i'.succ (Fin.last b) (by simp) (by simp)
      simp only [t, Fin.append_left, Fin.append_right, e1, e2, e3]
      have := congrFun htl i'
      simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, r] at this
      rw [this]
      ring
    | right i'' =>
      have e1 : ∀ jl : Fin k, N (Fin.natAdd k i'').succ (Fin.castSucc (Fin.castAdd b jl)) = 0 :=
        fun jl => N_bl _ _ i''.succ jl (by simp; omega) (by simp) (by simp)
      have e2 : ∀ jr : Fin b, N (Fin.natAdd k i'').succ (Fin.castSucc (Fin.natAdd k jr)) =
          properMatrixOf h B i'' jr := fun jr =>
        N_br _ _ i''.succ jr.castSucc (by simp; omega) (by simp) (by simp)
      have e3 : N (Fin.natAdd k i'').succ (Fin.last (k + b)) = topVecOf h B i'' := 
        N_br _ _ i''.succ (Fin.last b) (by simp; omega) (by simp) (by simp)
      simp only [t, Fin.append_left, Fin.append_right, e1, e2, e3, zero_mul,
        Finset.sum_const_zero, zero_add]
      have := congrFun hg i''
      simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at this
      rw [this]
      ring
  have hA := det_eq_of_eliminated_column M1 t hcond
  -- the minor is block triangular
  have hZ : (M1.submatrix Fin.succ Fin.castSucc) =
      N.submatrix Fin.succ Fin.castSucc := by
    ext i j
    simp only [Matrix.submatrix_apply]
    exact hM1row i _
  have hblock : (N.submatrix Fin.succ Fin.castSucc).det =
      (properMatrixOf h K).det * (properMatrixOf h B).det := by
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
    have : (N.submatrix Fin.succ Fin.castSucc).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (properMatrixOf h K)
          (Matrix.of fun (i : Fin k) (j : Fin b) => capEntry h K B i.succ j.castSucc) 0
          (properMatrixOf h B) := by
      ext x y
      rcases x with i | i <;> rcases y with j | j
      · exact N_tl _ _ i.succ j (by simp) (by simp)
      · exact N_tr _ _ i.succ j.castSucc (by simp) (by simp)
      · exact N_bl _ _ i.succ j (by simp; omega) (by simp) (by simp)
      · exact N_br _ _ i.succ j.castSucc (by simp; omega) (by simp) (by simp)
    rw [this, Matrix.det_fromBlocks_zero₂₁]
  have hE : M1 0 (Fin.last (k + b)) + ∑ j, M1 0 j.castSucc * t j =
      topCombo h K B w (Fin.last b) + ∑ j : Fin b, topCombo h K B w j.castSucc * g j := by
    rw [right0 (Fin.last b) _ (by simp), Fin.sum_univ_add]
    simp only [t, Fin.append_left, Fin.append_right, left0, zero_mul, Finset.sum_const_zero,
      zero_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [right0 j.castSucc _ (by simp)]
  have hS : schurOf h (splice K B hK hB) = N.det := rfl
  rw [hS, ← hdet1, hA, hZ, hblock, hE]
  simp only [cornerOf]
  rw [pow_add]
  ring

theorem leftExp_cast (i : Fin k) : (leftExp K i : ℤ) = K.row 0 - K.row i.succ := by
  have := K.row_strictAnti (Fin.succ_pos i)
  unfold leftExp
  omega

theorem colPos_cast_of_norm (hB : IsNorm B) (j : Fin b) : (colPos B j : ℤ) = B.col j.castSucc := by
  have h1 := col_pos_of_ne_last B hB j.castSucc (Fin.castSucc_lt_last j).ne
  unfold colPos
  have : B.col (Fin.last b) = 0 := hB
  omega

/-- The top row after the row operation is the coefficient series of `H C_K`, read as letters. -/
theorem topCombo_eq (hK : IsNorm K) (hB : IsNorm B) (w : Fin k → L) (y : Fin (b + 1)) :
    topCombo h K B w y =
      letterOf (fun m => PowerSeries.coeff m (PowerSeries.mk h *
        (capPoly w (leftExp K) : PowerSeries L))) (B.row 0 + K.row 0 - B.col y) := by
  have hc := top_pos B hB
  have ha := top_pos K hK
  have hy : B.col y < B.row 0 := by
    have h1 := B.col_strictAnti.antitone (Fin.zero_le y)
    have h2 := B.row_nonempty 0
    omega
  have hn : 0 ≤ B.row 0 + K.row 0 - B.col y := by omega
  rw [letterOf_coeff _ hn, coeff_mk_mul_capPoly]
  unfold topCombo capEntry
  rw [letterOf_nonneg_eq h hn]
  have hnat : (((B.row 0 + K.row 0 - B.col y).toNat : ℕ) : ℤ) = B.row 0 + K.row 0 - B.col y :=
    Int.toNat_of_nonneg hn
  rw [hnat]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [leftExp_cast]
  congr 2
  ring

/-- **The splice identity** (`sc:splice-identity`): `s_{K ◁ B} = κ_K κ_B [z^{c+a}] H C_K G_B`,
for any left vector `w` and right vector `g` solving the proper systems. -/
theorem schurOf_splice (w : Fin k → L) (g : Fin b → L)
    (hw : w ᵥ* properMatrixOf h K = -topRowOf h K)
    (hg : properMatrixOf h B *ᵥ g = -topVecOf h B)
    (hKu : IsUnit (properMatrixOf h K).det) :
    schurOf h (splice K B hK hB) = cornerOf h K * cornerOf h B *
      PowerSeries.coeff (B.row 0 + K.row 0).toNat (PowerSeries.mk h *
        ((capPoly w (leftExp K) * capPoly g (colPos B) : L[X]) : PowerSeries L)) := by
  rw [schurOf_splice_aux w g hw hg hKu]
  congr 1
  have hc := top_pos B hB
  have ha := top_pos K hK
  have hmul : PowerSeries.mk h * ((capPoly w (leftExp K) * capPoly g (colPos B) : L[X]) :
      PowerSeries L) = PowerSeries.mk (fun m => PowerSeries.coeff m (PowerSeries.mk h *
        (capPoly w (leftExp K) : PowerSeries L))) * (capPoly g (colPos B) : PowerSeries L) := by
    rw [Polynomial.coe_mul, ← mul_assoc]
    congr 1
    ext m
    simp
  rw [hmul, coeff_mk_mul_capPoly]
  have hN : (((B.row 0 + K.row 0).toNat : ℕ) : ℤ) = B.row 0 + K.row 0 :=
    Int.toNat_of_nonneg (by omega)
  have h0 : B.col (Fin.last b) = 0 := hB
  rw [topCombo_eq hK hB, h0, sub_zero,
    ← letterOf_coeff (PowerSeries.mk h * (capPoly w (leftExp K) : PowerSeries L))
      (show 0 ≤ B.row 0 + K.row 0 by omega)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [topCombo_eq hK hB, mul_comm, hN, colPos_cast_of_norm hB]

end Main

end SkewCoframeRigidity.FixedCap
