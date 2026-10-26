/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadSelect

/-!
# The gap numerator is an actual Schur function

The gap case of `sc:linearized-cap` in `shields-2026-skew-coframe-rigidity.tex`
(`sc:gap-coface`).  With `m = X_0`, the prefix `P` has rows `X_1, …, X_p` and columns
`Y_0, …, Y_{p-1}`, and the differentiated top equation reads
`ρ_b (h_{m-b} - H_{m,cols P} P⁻¹ H_{rows P,b}) = 0`.  Multiplied by `det P`, the factor is
`gapNumerator`, with no inverse.

* `gapBoard` is the actual diagram with rows `X_0, …, X_p` and columns `Y_0, …, Y_{p-1}, b`;
  it is connected and zero-free when the prefix is closed, and `gapBoard_schur` says its Schur
  function is `(-1)^p · gapNumerator`.
* `gap_case_of_equation` turns the equation `C ρ_b · gapNumerator = 0`, the output of the
  `h_b`-derivative of the top equation, into the gap disjunct of `linearized_head_step`.

Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe MvPolynomial Matrix

variable {n p : ℕ}

section Board

variable (B : BetaDiagram (n + 1)) (hp : p ≤ n) (b : ℤ)

/-- The columns of the gap diagram: `Y_0, …, Y_{p-1}`, then `b`. -/
def gapCol (j : Fin (p + 1)) : ℤ := if h : j.val < p then B.col ⟨j.val, by omega⟩ else b

/-- The actual diagram with rows `X_0, …, X_p` and columns `Y_0, …, Y_{p-1}, b`. -/
def gapBoard (hb : ∀ j : Fin (n + 1), j.val < p → b < B.col j) (hbp : b < B.row ⟨p, by omega⟩)
    : BetaDiagram (p + 1) where
  row i := B.row ⟨i.val, by omega⟩
  col := gapCol B hp b
  row_strictAnti := by
    intro i j hij
    exact B.row_strictAnti
      (show (⟨i.val, by omega⟩ : Fin (n + 1)) < ⟨j.val, by omega⟩ from hij)
  col_strictAnti := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hi : i.val < p := by omega
    by_cases hj : j.val < p
    · have := B.col_strictAnti
        (show (⟨i.val, by omega⟩ : Fin (n + 1)) < ⟨j.val, by omega⟩ from hij')
      simp only [gapCol, hi, hj, ↓reduceDIte]; exact this
    · have := hb ⟨i.val, by omega⟩ hi
      simp only [gapCol, hi, hj, ↓reduceDIte]; exact this
  row_nonempty := by
    intro i
    by_cases hi : i.val < p
    · have := B.row_nonempty ⟨i.val, by omega⟩
      simp only [gapCol, hi, ↓reduceDIte]; exact this
    · have hip : i.val = p := by omega
      simp only [gapCol, hi, ↓reduceDIte]
      have : B.row ⟨i.val, by omega⟩ = B.row ⟨p, by omega⟩ := by congr 1; exact Fin.ext hip
      rw [this]; exact hbp

variable (hb : ∀ j : Fin (n + 1), j.val < p → b < B.col j) (hbp : b < B.row ⟨p, by omega⟩)

theorem gapBoard_connected (hBc : B.Connected) :
    (gapBoard B hp b hb hbp).Connected := by
  refine ⟨by omega, fun i hi => ?_⟩
  have hip : i.val < p := by omega
  change gapCol B hp b i ≤ B.row ⟨i.val + 1, by omega⟩
  simp only [gapCol, hip, ↓reduceDIte]
  exact hBc.2 ⟨i.val, by omega⟩ (by simp only; omega)

theorem gapBoard_zeroFree (hBz : ZeroFree B) (hbr : ∀ i, B.row i ≠ b) :
    ZeroFree (gapBoard B hp b hb hbp) := by
  intro i j
  change B.row ⟨i.val, by omega⟩ ≠ gapCol B hp b j
  by_cases hj : j.val < p
  · simp only [gapCol, hj, ↓reduceDIte]; exact hBz _ _
  · simp only [gapCol, hj, ↓reduceDIte]; exact hbr _

end Board

section Numerator

variable (B : BetaDiagram (n + 1)) (hp : p ≤ n) (b : ℤ)

/-- The prefix matrix `P`: rows `X_1, …, X_p`, columns `Y_0, …, Y_{p-1}`. -/
noncomputable def gapPrefixMat : Matrix (Fin p) (Fin p) CompleteRing :=
  Matrix.of fun i j => complete (B.row ⟨i.val + 1, by omega⟩ - B.col ⟨j.val, by omega⟩)

/-- The column `H_{rows P, b}`. -/
noncomputable def gapColVec : Fin p → CompleteRing :=
  fun i => complete (B.row ⟨i.val + 1, by omega⟩ - b)

/-- The row `H_{m, cols P}`, `m = X_0`. -/
noncomputable def gapRowVec : Fin p → CompleteRing :=
  fun j => complete (B.row 0 - B.col ⟨j.val, by omega⟩)

/-- `det P · (h_{m-b} - H_{m,cols P} P⁻¹ H_{rows P,b})`, with `P⁻¹` replaced by `adj P`. -/
noncomputable def gapNumerator : CompleteRing :=
  complete (B.row 0 - b) * (gapPrefixMat B hp).det -
    gapRowVec B hp ⬝ᵥ ((gapPrefixMat B hp).adjugate *ᵥ gapColVec B hp b)

variable (hb : ∀ j : Fin (n + 1), j.val < p → b < B.col j) (hbp : b < B.row ⟨p, by omega⟩)

/-- The matrix of the gap diagram is the bordered matrix of `P`, with the top row moved to the
bottom and the last column placed last. -/
theorem gapBoard_matrix :
    (gapBoard B hp b hb hbp).matrix =
      (bordered (gapPrefixMat B hp) (gapColVec B hp b) (gapRowVec B hp)
          (complete (B.row 0 - b))).submatrix
        (fun i : Fin (p + 1) => Fin.cases (Sum.inr ()) (fun k => Sum.inl k) i)
        (fun j : Fin (p + 1) => Fin.lastCases (Sum.inr ()) (fun k => Sum.inl k) j) := by
  refine Matrix.ext fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [bordered, gapBoard, gapCol, BetaDiagram.matrix]
  · simp [bordered, gapBoard, gapCol, BetaDiagram.matrix, gapRowVec]
  · simp [bordered, gapBoard, gapCol, BetaDiagram.matrix, gapColVec]
  · simp [bordered, gapBoard, gapCol, BetaDiagram.matrix, gapPrefixMat]

/-- The Schur function of the gap diagram is `(-1)^p` times the gap numerator. -/
theorem gapBoard_schur :
    (gapBoard B hp b hb hbp).schur = (-1) ^ p * gapNumerator B hp b := by
  unfold BetaDiagram.schur
  rw [gapBoard_matrix]
  let ι : Fin (p + 1) ≃ Fin p ⊕ Unit :=
    (finSumFinEquiv (m := p) (n := 1)).symm.trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique (Fin 1) Unit))
  have hι : ∀ j : Fin (p + 1), ι j = Fin.lastCases (Sum.inr ()) (fun k => Sum.inl k) j := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [ι]
    · simp [ι]
  have hcol : (fun j : Fin (p + 1) => Fin.lastCases (Sum.inr ()) (fun k => Sum.inl k) j) = ι := by
    funext j; exact (hι j).symm
  have hrow : (fun i : Fin (p + 1) => Fin.cases (Sum.inr ()) (fun k => Sum.inl k) i) =
      ι ∘ (finRotate (p + 1)).symm := by
    funext i
    have hs0 : (finRotate (p + 1)).symm 0 = Fin.last p := by
      rw [Equiv.symm_apply_eq]; exact (finRotate_last (n := p)).symm
    have hs1 : ∀ k : Fin p, (finRotate (p + 1)).symm k.succ = k.castSucc := by
      intro k
      rw [Equiv.symm_apply_eq, finRotate_of_lt (by simp)]
      ext; simp
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [hs0, hι]
    · simp [hs1, hι]
  rw [hcol, hrow]
  set M := bordered (gapPrefixMat B hp) (gapColVec B hp b) (gapRowVec B hp)
    (complete (B.row 0 - b))
  have h1 : M.submatrix (ι ∘ (finRotate (p + 1)).symm) ι =
      (M.submatrix ι ι).submatrix (finRotate (p + 1)).symm id := rfl
  rw [h1, Matrix.det_permute, Matrix.det_submatrix_equiv_self ι M, det_bordered]
  have h2 : (Equiv.Perm.sign (finRotate (p + 1)).symm : ℤˣ) = (-1) ^ p := by
    rw [Equiv.Perm.sign_symm, sign_finRotate]; simp
  rw [h2]
  simp [gapNumerator]

/-- The gap equation `ρ_b · (gap numerator) = 0` yields the gap disjunct of
`linearized_head_step`: `ρ_b · s_G = 0` for the actual diagram `G = gapBoard`. -/
theorem gap_disjunct (ρ : ℤ →₀ ℚ) (hρb : ρ b ≠ 0)
    (hb : ∀ j : Fin (n + 1), j.val < p → b < B.col j) (hbp : b < B.row ⟨p, by omega⟩)
    (heq : C (ρ b) * gapNumerator B hp b = 0) :
    ∃ (g : ℕ) (G : BetaDiagram (g + 1)) (x : ℤ), ρ x ≠ 0 ∧ C (ρ x) * G.schur = 0 :=
  ⟨p, gapBoard B hp b hb hbp, b, hρb, by
    rw [gapBoard_schur]
    linear_combination ((-1 : CompleteRing) ^ p) * heq⟩

end Numerator

end SkewCoframeRigidity.UnitRestoration
