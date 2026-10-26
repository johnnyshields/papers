/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.Bordered
import SkewCoframeRigidity.UnitRestoration.VacancyPulse
import SkewCoframeRigidity.FixedCap.SpliceIdentity
import SkewCoframeRigidity.Coframe.Algebra
import SkewCoframeRigidity.FixedCap.Reduction

/-!
# The first variation of the coframe

Formalizes the differentiated top equation in the proof of `sc:linearized-cap` of
`shields-2026-skew-coframe-rigidity.tex` (`sc:restoration-polynomial`, `sc:linearized-coframe`,
`sc:linearized-observations`).  For a matrix `[[t, e], [T, f]]` with a top row and a last
column, the bordered derivative `ṡ^{(b)} = -b adj(M) a` is, by Cramer on the bordered proper
system,
`(-1)^n det T · (-(w ⬝ T⁻¹ v) [HG]_m - α₀ P_b)`, where `[HG]_m` is the top quotient and
`-α₀ P_b = [H δ^{(b)}]_m` is the top coefficient of the vacancy pulse.  This file proves the
identity at the level of matrices with an arbitrary solution pair `(g, y)` of the proper system,
then for a normalized diagram.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open Matrix Polynomial SkewCoframeRigidity.Coframe

variable {F : Type*} [Field F] {n : ℕ}

/-- The equivalence `Fin m ⊕ Unit ≃ Fin (m + 1)` placing the extra index last. -/
def sumUnitEquiv (m : ℕ) : Fin m ⊕ Unit ≃ Fin (m + 1) where
  toFun := Sum.elim Fin.castSucc fun _ => Fin.last m
  invFun := Fin.lastCases (Sum.inr ()) Sum.inl
  left_inv := by
    rintro (i | ⟨⟩) <;> simp
  right_inv := by
    intro i
    induction i using Fin.lastCases <;> simp

/-- **Cramer on the bordered proper system.**  Let `M = [[t, e], [T, f]]` have top row `(t, e)`
and proper block `(T, f)`, and let `a = (a₀; v)`, `b = (w, b₀)` be the border.  If `g` solves
`T g = -f` and `y` solves `T y = v`, then
`-b ⬝ adj(M) a = (-1)^n det T (-(w ⬝ y)(e + t ⬝ g) - (a₀ - t ⬝ y)(b₀ + w ⬝ g))`. -/
theorem bordered_identity (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (T : Matrix (Fin n) (Fin n) F)
    (t w f v g y : Fin n → F) (e a₀ b₀ : F) (a b : Fin (n + 1) → F)
    (hMt : ∀ j, M 0 j.castSucc = t j) (hMe : M 0 (Fin.last n) = e)
    (hMT : ∀ i j, M i.succ j.castSucc = T i j) (hMf : ∀ i, M i.succ (Fin.last n) = f i)
    (ha₀ : a 0 = a₀) (hav : ∀ i, a i.succ = v i) (hbw : ∀ j, b j.castSucc = w j)
    (hb₀ : b (Fin.last n) = b₀) (hg : T *ᵥ g = -f) (hy : T *ᵥ y = v) :
    -(b ⬝ᵥ (M.adjugate *ᵥ a)) = (-1) ^ n * T.det *
      (-((w ⬝ᵥ y) * (e + t ⬝ᵥ g)) - (a₀ - t ⬝ᵥ y) * (b₀ + w ⬝ᵥ g)) := by
  set c : F := w ⬝ᵥ y with hc
  have hdet := det_bordered M a b c
  -- the unbordered determinant
  have hM : M.det = (-1) ^ n * T.det * (e + t ⬝ᵥ g) := by
    have hcond : ∀ i : Fin n, ∑ j, M i.succ j.castSucc * g j + M i.succ (Fin.last n) = 0 := by
      intro i
      have := congrFun hg i
      simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at this
      simp only [hMT, hMf]
      linear_combination this
    rw [FixedCap.det_eq_of_eliminated_column M g hcond]
    have hsub : M.submatrix Fin.succ Fin.castSucc = T := by
      ext i j; simp [hMT]
    rw [hsub, hMe]
    simp only [hMt, dotProduct]
  -- the bordered determinant, with the border row eliminated by the choice of `c`
  let N : Matrix (Fin (n + 1) ⊕ Unit) (Fin (n + 1) ⊕ Unit) F := bordered M a b c
  let e1 : Fin (n + 2) ≃ Fin (n + 1) ⊕ Unit := (sumUnitEquiv (n + 1)).symm
  let N2 : Matrix (Fin (n + 2)) (Fin (n + 2)) F := N.submatrix e1 e1
  have hN2 : N2.det = N.det := Matrix.det_submatrix_equiv_self e1 N
  have e1c : ∀ i : Fin (n + 1), e1 i.castSucc = Sum.inl i := fun i => by simp [e1, sumUnitEquiv]
  have e1l : e1 (Fin.last (n + 1)) = Sum.inr () := by simp [e1, sumUnitEquiv]
  let t' : Fin (n + 1) → F := Fin.lastCases 0 fun j => -y j
  have hcond2 : ∀ i : Fin (n + 1), ∑ j, N2 i.succ j.castSucc * t' j +
      N2 i.succ (Fin.last (n + 1)) = 0 := by
    intro i
    rw [Fin.sum_univ_castSucc]
    simp only [t', Fin.lastCases_last, Fin.lastCases_castSucc, mul_zero, add_zero]
    induction i using Fin.lastCases with
    | last =>
      simp only [N2, N, Fin.succ_last, Matrix.submatrix_apply, e1c, e1l, bordered,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.replicateRow_apply,
        Matrix.of_apply, hbw]
      simp only [hc, dotProduct, Finset.sum_neg_distrib, mul_neg]
      ring
    | cast i' =>
      simp only [N2, N, Fin.succ_castSucc, Matrix.submatrix_apply, e1c, e1l, bordered,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.replicateCol_apply, hMT, hav]
      have := congrFun hy i'
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [mul_neg, Finset.sum_neg_distrib]
      linear_combination -this
  have hN2e := FixedCap.det_eq_of_eliminated_column N2 t' hcond2
  have hlast : N2 0 (Fin.last (n + 1)) + ∑ j, N2 0 j.castSucc * t' j = a₀ - t ⬝ᵥ y := by
    rw [Fin.sum_univ_castSucc]
    have h0 : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
    simp only [t', Fin.lastCases_last, Fin.lastCases_castSucc, mul_zero, add_zero]
    simp only [N2, N, h0, Matrix.submatrix_apply, e1c, e1l, bordered, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.replicateCol_apply, ha₀, hMt]
    simp only [dotProduct, mul_neg, Finset.sum_neg_distrib]
    ring
  -- the minor is the bordered determinant of `T`
  let Nb : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) F := bordered T f w b₀
  have hminor : N2.submatrix Fin.succ Fin.castSucc =
      Nb.submatrix (sumUnitEquiv n).symm (sumUnitEquiv n).symm := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp [N2, N, Nb, e1c, e1l, bordered, sumUnitEquiv, hb₀]
      | cast j' =>
        simp [N2, N, Nb, e1c, e1l, bordered, sumUnitEquiv, hbw]
    | cast i' =>
      induction j using Fin.lastCases with
      | last =>
        simp only [N2, N, Nb, Matrix.submatrix_apply, Fin.succ_castSucc, e1c, bordered]
        simp [sumUnitEquiv, hMf]
      | cast j' =>
        simp only [N2, N, Nb, Matrix.submatrix_apply, Fin.succ_castSucc, e1c, bordered]
        simp [sumUnitEquiv, hMT]
  have hminordet : (N2.submatrix Fin.succ Fin.castSucc).det = T.det * (b₀ + w ⬝ᵥ g) := by
    rw [hminor, Matrix.det_submatrix_equiv_self (sumUnitEquiv n).symm Nb]
    simp only [Nb]
    rw [det_bordered]
    have hadj : T.adjugate *ᵥ f = -(T.det • g) := by
      have : f = -(T *ᵥ g) := by rw [hg]; simp
      rw [this, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [hadj]
    simp only [dotProduct_neg, dotProduct_smul, smul_eq_mul]
    ring
  have hNdet : N.det = (-1) ^ (n + 1) * (T.det * (b₀ + w ⬝ᵥ g)) * (a₀ - t ⬝ᵥ y) := by
    rw [← hN2, hN2e, hminordet, hlast]
  have : -(b ⬝ᵥ (M.adjugate *ᵥ a)) = N.det - c * M.det := by
    have : N.det = c * M.det - b ⬝ᵥ (M.adjugate *ᵥ a) := hdet
    linear_combination -this
  rw [this, hNdet, hM, pow_succ]
  ring

/-- The coefficient of a series against the vacancy pulse of another letter sequence. -/
theorem coeff_series_mul_pulse' (U V : ℕ → F) (I S : Fin n → ℕ) (p : F) (b k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk U * (pulse V I S p b : PowerSeries F)) =
      -p * (letterOf U ((k : ℤ) - b) -
        ∑ s, ((properMat V I S)⁻¹ *ᵥ vacancyVec V I b) s * letterOf U ((k : ℤ) - S s)) := by
  unfold pulse
  rw [Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm, PowerSeries.coeff_C_mul]
  congr 1
  rw [Polynomial.coe_sub, mul_sub, map_sub, coeff_series_mul_monomial]
  congr 1
  rw [show ((∑ s, Polynomial.C (((properMat V I S)⁻¹ *ᵥ vacancyVec V I b) s) *
      Polynomial.X ^ S s : F[X]) : PowerSeries F) = ∑ s, ((Polynomial.C
      (((properMat V I S)⁻¹ *ᵥ vacancyVec V I b) s) * Polynomial.X ^ S s : F[X]) : PowerSeries F)
    from map_sum (Polynomial.coeToPowerSeries.ringHom (R := F)) _ _, Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => coeff_series_mul_C_monomial _ _ _ _

section Diagram

open SkewCoframeRigidity SkewCoframeRigidity.Coframe SkewCofactorIndependence

variable {N : ℕ}

/-- The column `a_b = (h_{x-b})_{x ∈ X_D}` of the restoration at `b`. -/
def vacCol (h : ℕ → F) (D : BetaDiagram N) (b : ℕ) : Fin N → F :=
  fun x => letterOf h (D.row x - b)

/-- The row `b_b = (h_{b-y})_{y ∈ Y_D}` of the restoration at `b`. -/
def vacRow (h : ℕ → F) (D : BetaDiagram N) (b : ℕ) : Fin N → F :=
  fun y => letterOf h ((b : ℤ) - D.col y)

/-- The restoration polynomial `ṡ^{(b)} = -b_b adj(M_D) a_b` (`sc:restoration-polynomial`). -/
def restorationPoly (h : ℕ → F) (D : BetaDiagram N) (b : ℕ) : F :=
  -(vacRow h D b ⬝ᵥ ((fullMatrixOf h D).adjugate *ᵥ vacCol h D b))

/-- The first variation of the signed proper corner: `κ̇^{(b)} = (-1)^n (-w_b adj(T) v_b)`. -/
def cornerDot (h : ℕ → F) (D : BetaDiagram (n + 1)) (b : ℕ) : F :=
  (-1) ^ n * -((fun j : Fin n => letterOf h ((b : ℤ) - D.col j.castSucc)) ⬝ᵥ
    ((properMatrixOf h D).adjugate *ᵥ fun i : Fin n => letterOf h (D.row i.succ - b)))

theorem properMat_eq (h : ℕ → F) (D : BetaDiagram (n + 1)) :
    properMat h (rowPos D) (colPos D) = properMatrixOf h D := by
  ext i j
  simp only [properMat, properMatrixOf, Matrix.of_apply]
  rw [rowPos_sub_colPos D]

theorem vacancyVec_eq (h : ℕ → F) (D : BetaDiagram (n + 1)) (hD : IsNorm D) (b : ℕ) :
    vacancyVec h (rowPos D) b = fun i : Fin n => letterOf h (D.row i.succ - b) := by
  ext i
  have h0 : D.col (Fin.last n) = 0 := hD
  simp only [vacancyVec]
  rw [rowPos_cast D, h0, sub_zero]

/-- `κ̇^{(b)}` through the solution `y = T⁻¹ v_b` of the vacancy system. -/
theorem cornerDot_eq (h : ℕ → F) (D : BetaDiagram (n + 1)) (b : ℕ) (y : Fin n → F)
    (hy : properMatrixOf h D *ᵥ y = fun i : Fin n => letterOf h (D.row i.succ - b)) :
    cornerDot h D b = cornerOf h D *
      -((fun j : Fin n => letterOf h ((b : ℤ) - D.col j.castSucc)) ⬝ᵥ y) := by
  have hadj : (properMatrixOf h D).adjugate *ᵥ (fun i : Fin n => letterOf h (D.row i.succ - b)) =
      (properMatrixOf h D).det • y := by
    rw [← hy, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  unfold cornerDot cornerOf
  rw [hadj, dotProduct_smul, smul_eq_mul]
  ring

/-- **Cramer on the bordered proper system** for a diagram: any solutions `g`, `y` of the proper
system and of the vacancy system give `ṡ^{(b)} = κ (-(w y)(e + t g) - (a₀ - t y)(b₀ + w g))`. -/
theorem restorationPoly_cramer (h : ℕ → F) (D : BetaDiagram (n + 1)) (b : ℕ) (g y : Fin n → F)
    (hg : properMatrixOf h D *ᵥ g = -topVecOf h D)
    (hy : properMatrixOf h D *ᵥ y = fun i : Fin n => letterOf h (D.row i.succ - b)) :
    restorationPoly h D b = cornerOf h D *
      (-(((fun j : Fin n => letterOf h ((b : ℤ) - D.col j.castSucc)) ⬝ᵥ y) *
          (letterOf h (D.row 0 - D.col (Fin.last n)) +
            (fun j => letterOf h (D.row 0 - D.col j.castSucc)) ⬝ᵥ g)) -
        (letterOf h (D.row 0 - b) - (fun j => letterOf h (D.row 0 - D.col j.castSucc)) ⬝ᵥ y) *
          (letterOf h ((b : ℤ) - D.col (Fin.last n)) +
            (fun j : Fin n => letterOf h ((b : ℤ) - D.col j.castSucc)) ⬝ᵥ g)) := by
  have key := bordered_identity (fullMatrixOf h D) (properMatrixOf h D)
    (fun j => letterOf h (D.row 0 - D.col j.castSucc))
    (fun j => letterOf h ((b : ℤ) - D.col j.castSucc)) (topVecOf h D)
    (fun i => letterOf h (D.row i.succ - b)) g y (letterOf h (D.row 0 - D.col (Fin.last n)))
    (letterOf h (D.row 0 - b)) (letterOf h ((b : ℤ) - D.col (Fin.last n)))
    (vacCol h D b) (vacRow h D b) (fun _ => rfl) rfl (fun _ _ => rfl) (fun _ => rfl) rfl
    (fun _ => rfl) (fun _ => rfl) rfl hg hy
  have : restorationPoly h D b = -(vacRow h D b ⬝ᵥ ((fullMatrixOf h D).adjugate *ᵥ vacCol h D b)) :=
    rfl
  rw [this, key]
  unfold cornerOf
  ring

theorem coeff_coframe_vac (h : ℕ → F) (D : BetaDiagram (n + 1)) (hD : IsNorm D) (b : ℕ) :
    PowerSeries.coeff b (PowerSeries.mk h * (coframeOf h D : PowerSeries F)) =
      letterOf h ((b : ℤ) - D.col (Fin.last n)) +
        (fun j : Fin n => letterOf h ((b : ℤ) - D.col j.castSucc)) ⬝ᵥ coframeVecOf h D := by
  have h0 : D.col (Fin.last n) = 0 := hD
  rw [coframeOf_eq_uniPoly, coeff_series_mul_uniPoly, h0, sub_zero, letterOf_natCast]
  congr 1
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, colPos_cast D, h0, sub_zero]

/-- **The differentiated top equation** (`sc:linearized-coframe`, `sc:linearized-observations`):
for a normalized diagram with invertible proper matrix, the bordered derivative at `b` is
`κ̇^{(b)} [HG]_M + κ [H δ^{(b)}]_M`, where `δ^{(b)}` is the vacancy pulse with
numerator coefficient `P_b = [HG]_b`. -/
theorem restorationPoly_eq (h : ℕ → F) (D : BetaDiagram (n + 1)) (hD : IsNorm D)
    (hT : (properMatrixOf h D).det ≠ 0) (b : ℕ) :
    restorationPoly h D b = cornerDot h D b * topQuotientOf h D + cornerOf h D *
      PowerSeries.coeff (span D) (PowerSeries.mk h *
        (pulse h (rowPos D) (colPos D)
          (PowerSeries.coeff b (PowerSeries.mk h * (coframeOf h D : PowerSeries F))) b :
          PowerSeries F)) := by
  have h0 : D.col (Fin.last n) = 0 := hD
  set T := properMatrixOf h D with hTdef
  set y : Fin n → F := T⁻¹ *ᵥ fun i : Fin n => letterOf h (D.row i.succ - b) with hy
  set g := coframeVecOf h D with hg
  have hgsol : T *ᵥ g = -topVecOf h D := properMatrix_mulVec_coframeVecOf h D hT
  have hysol : T *ᵥ y = fun i : Fin n => letterOf h (D.row i.succ - b) := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hT),
      Matrix.one_mulVec]
  have hlab : D.largestLabel = D.row 0 - D.col (Fin.last n) := rfl
  have hspanc : (span D : ℤ) = D.row 0 := by rw [span_cast D, hlab, h0, sub_zero]
  have hcolPos : ∀ j : Fin n, (colPos D j : ℤ) = D.col j.castSucc := fun j => by
    rw [colPos_cast D, h0, sub_zero]
  have htq : topQuotientOf h D = letterOf h (D.row 0 - D.col (Fin.last n)) +
      (fun j => letterOf h (D.row 0 - D.col j.castSucc)) ⬝ᵥ g := by
    unfold topQuotientOf seriesOf
    rw [coframeOf_eq_uniPoly, coeff_span h D g, hlab]
    congr 1
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hPb := coeff_coframe_vac h D hD b
  have hpulse : PowerSeries.coeff (span D) (PowerSeries.mk h *
      (pulse h (rowPos D) (colPos D)
        (PowerSeries.coeff b (PowerSeries.mk h * (coframeOf h D : PowerSeries F))) b :
        PowerSeries F)) =
      -(PowerSeries.coeff b (PowerSeries.mk h * (coframeOf h D : PowerSeries F))) *
        (letterOf h (D.row 0 - b) -
          (fun j => letterOf h (D.row 0 - D.col j.castSucc)) ⬝ᵥ y) := by
    rw [coeff_series_mul_pulse, properMat_eq, vacancyVec_eq h D hD, hspanc]
    congr 2
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hy, mul_comm]
    congr 2
    rw [hcolPos j]
  rw [restorationPoly_cramer h D b g y hgsol hysol, cornerDot_eq h D b y hysol, hpulse, htq, hPb]
  ring

/-- **The weighted differentiated top equation**: `∑_b ρ_b ṡ^{(b)} = κ̇ [HG]_M + κ [HQ]_M` for the
first variation `Q = ∑_b ρ_b δ^{(b)}` of the coframe and `κ̇ = ∑_b ρ_b κ̇^{(b)}`. -/
theorem restorationSum_eq {m : ℕ} (h : ℕ → F) (D : BetaDiagram (n + 1)) (hD : IsNorm D)
    (hT : (properMatrixOf h D).det ≠ 0) (bpos : Fin m → ℕ) (ρ : Fin m → F) :
    ∑ v, ρ v * restorationPoly h D (bpos v) =
      (∑ v, ρ v * cornerDot h D (bpos v)) * topQuotientOf h D + cornerOf h D *
        PowerSeries.coeff (span D) (PowerSeries.mk h *
          (pulseSum h (rowPos D) (colPos D)
            bpos (fun v => PowerSeries.coeff (bpos v) (PowerSeries.mk h *
              (coframeOf h D : PowerSeries F))) ρ : PowerSeries F)) := by
  have hlin : PowerSeries.coeff (span D) (PowerSeries.mk h *
      (pulseSum h (rowPos D) (colPos D) bpos (fun v => PowerSeries.coeff (bpos v)
        (PowerSeries.mk h * (coframeOf h D : PowerSeries F))) ρ : PowerSeries F)) =
      ∑ v, ρ v * PowerSeries.coeff (span D) (PowerSeries.mk h *
        (pulse h (rowPos D) (colPos D) (PowerSeries.coeff (bpos v) (PowerSeries.mk h *
          (coframeOf h D : PowerSeries F))) (bpos v) : PowerSeries F)) := by
    unfold pulseSum
    rw [show ((∑ v, Polynomial.C (ρ v) * pulse h (rowPos D) (colPos D) _ (bpos v) : F[X]) :
        PowerSeries F) = ∑ v, ((Polynomial.C (ρ v) * pulse h (rowPos D) (colPos D) _ (bpos v) :
        F[X]) : PowerSeries F) from
      map_sum (Polynomial.coeToPowerSeries.ringHom (R := F)) _ _, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm, PowerSeries.coeff_C_mul]
  rw [hlin]
  have hv : ∀ v, ρ v * restorationPoly h D (bpos v) = ρ v * cornerDot h D (bpos v) *
      topQuotientOf h D + cornerOf h D * (ρ v * PowerSeries.coeff (span D) (PowerSeries.mk h *
        (pulse h (rowPos D) (colPos D) (PowerSeries.coeff (bpos v) (PowerSeries.mk h *
          (coframeOf h D : PowerSeries F))) (bpos v) : PowerSeries F))) := fun v => by
    rw [restorationPoly_eq h D hD hT]
    ring
  simp only [hv, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

end Diagram

section SpliceEntries

open SkewCoframeRigidity SkewCoframeRigidity.Coframe SkewCoframeRigidity.FixedCap
  SkewCofactorIndependence

variable {k b : ℕ} (h : ℕ → F) (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
  (hK : IsNorm K) (hB : IsNorm B)

theorem sp_tl (i j : Fin k) :
    properMatrixOf h (splice K B hK hB) (Fin.castAdd b i) (Fin.castAdd b j) =
      properMatrixOf h K i j :=
  N_tl (h := h) (hK := hK) (hB := hB) _ _ i.succ j (by simp) (by simp)

theorem sp_tr (i : Fin k) (j : Fin b) :
    properMatrixOf h (splice K B hK hB) (Fin.castAdd b i) (Fin.natAdd k j) =
      capEntry h K B i.succ j.castSucc :=
  N_tr (h := h) (hK := hK) (hB := hB) _ _ i.succ j.castSucc (by simp) (by simp)

theorem sp_bl (i : Fin b) (j : Fin k) :
    properMatrixOf h (splice K B hK hB) (Fin.natAdd k i) (Fin.castAdd b j) = 0 :=
  N_bl (h := h) (hK := hK) (hB := hB) _ _ i.succ j (by simp; omega) (by simp) (by simp)

theorem sp_br (i j : Fin b) :
    properMatrixOf h (splice K B hK hB) (Fin.natAdd k i) (Fin.natAdd k j) =
      properMatrixOf h B i j :=
  N_br (h := h) (hK := hK) (hB := hB) _ _ i.succ j.castSucc (by simp; omega) (by simp) (by simp)

theorem sp_f_top (i : Fin k) :
    topVecOf h (splice K B hK hB) (Fin.castAdd b i) = capEntry h K B i.succ (Fin.last b) :=
  N_tr (h := h) (hK := hK) (hB := hB) _ _ i.succ (Fin.last b) (by simp) (by simp)

theorem sp_f_bot (i : Fin b) :
    topVecOf h (splice K B hK hB) (Fin.natAdd k i) = topVecOf h B i :=
  N_br (h := h) (hK := hK) (hB := hB) _ _ i.succ (Fin.last b) (by simp; omega) (by simp)
    (by simp)

theorem sp_top_tl (j : Fin k) :
    letterOf h ((splice K B hK hB).row 0 - (splice K B hK hB).col (Fin.castAdd b j).castSucc) =
      topRowOf h K j :=
  N_tl (h := h) (hK := hK) (hB := hB) 0 _ 0 j (by simp) (by simp)

theorem sp_top_tr (j : Fin b) :
    letterOf h ((splice K B hK hB).row 0 - (splice K B hK hB).col (Fin.natAdd k j).castSucc) =
      capEntry h K B 0 j.castSucc :=
  N_tr (h := h) (hK := hK) (hB := hB) 0 _ 0 j.castSucc (by simp) (by simp)

theorem sp_top_last :
    letterOf h ((splice K B hK hB).row 0 - (splice K B hK hB).col (Fin.last (k + b))) =
      capEntry h K B 0 (Fin.last b) :=
  N_tr (h := h) (hK := hK) (hB := hB) 0 _ 0 (Fin.last b) (by simp) (by simp)

/-- The block `X` of crossing entries of the proper matrix of the splice. -/
def crossBlock : Matrix (Fin k) (Fin b) F :=
  Matrix.of fun i j => capEntry h K B i.succ j.castSucc

theorem sp_mulVec_left (zK : Fin k → F) (zB : Fin b → F) (i : Fin k) :
    (properMatrixOf h (splice K B hK hB) *ᵥ (Fin.append zK zB : Fin (k + b) → F))
        (Fin.castAdd b i) =
      (properMatrixOf h K *ᵥ zK) i + (crossBlock h K B *ᵥ zB) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    sp_tl h K B hK hB, sp_tr h K B hK hB, crossBlock, Matrix.of_apply]

theorem sp_mulVec_right (zK : Fin k → F) (zB : Fin b → F) (i : Fin b) :
    (properMatrixOf h (splice K B hK hB) *ᵥ (Fin.append zK zB : Fin (k + b) → F))
        (Fin.natAdd k i) = (properMatrixOf h B *ᵥ zB) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    sp_bl h K B hK hB, sp_br h K B hK hB, zero_mul, Finset.sum_const_zero, zero_add]

theorem sp_det_proper :
    (properMatrixOf h (splice K B hK hB)).det =
      (properMatrixOf h K).det * (properMatrixOf h B).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  have : (properMatrixOf h (splice K B hK hB)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (properMatrixOf h K) (crossBlock h K B) 0 (properMatrixOf h B) := by
    ext x y
    rcases x with i | i <;> rcases y with j | j
    · exact sp_tl h K B hK hB i j
    · exact sp_tr h K B hK hB i j
    · exact sp_bl h K B hK hB i j
    · exact sp_br h K B hK hB i j
  rw [this, Matrix.det_fromBlocks_zero₂₁]

theorem sp_corner :
    cornerOf h (splice K B hK hB) = cornerOf h K * cornerOf h B := by
  unfold cornerOf
  rw [sp_det_proper, pow_add]
  ring

theorem sp_vac_top (β : ℕ) (i : Fin k) :
    letterOf h ((splice K B hK hB).row (Fin.castAdd b i).succ - β) =
      letterOf h (B.row 0 + K.row i.succ - β) := by
  change letterOf h (spliceRow K B (Fin.castAdd b i).succ - β) = _
  rw [spliceRow_top K B _ (by simp)]
  have e : (⟨(Fin.castAdd b i).succ.val, by simp⟩ : Fin (k + 1)) = i.succ := Fin.ext (by simp)
  rw [e]

theorem sp_vac_bot (β : ℕ) (i : Fin b) :
    letterOf h ((splice K B hK hB).row (Fin.natAdd k i).succ - β) =
      letterOf h (B.row i.succ - β) := by
  change letterOf h (spliceRow K B (Fin.natAdd k i).succ - β) = _
  rw [spliceRow_bot K B _ (by simp)]
  have e : (⟨(Fin.natAdd k i).succ.val - k, by simp; omega⟩ : Fin (b + 1)) = i.succ :=
    Fin.ext (by simp; omega)
  rw [e]

theorem sp_vac_zero (β : ℕ) :
    letterOf h ((splice K B hK hB).row 0 - β) = letterOf h (B.row 0 + K.row 0 - β) := by
  rw [splice_span K B hK hB]

theorem sp_row_top (β : ℕ) (hβ : (β : ℤ) < B.row 0) (j : Fin k) :
    letterOf h ((β : ℤ) - (splice K B hK hB).col (Fin.castAdd b j).castSucc) = 0 := by
  change letterOf h ((β : ℤ) - spliceCol K B (Fin.castAdd b j).castSucc) = 0
  rw [spliceCol_top K B _ (by simp)]
  have e : (⟨(Fin.castAdd b j).castSucc.val, by simp⟩ : Fin (k + 1)) = j.castSucc :=
    Fin.ext (by simp)
  rw [e]
  have := col_nonneg K hK j.castSucc
  exact letterOf_neg_eq h (by omega)

theorem sp_row_bot (β : ℕ) (j : Fin b) :
    letterOf h ((β : ℤ) - (splice K B hK hB).col (Fin.natAdd k j).castSucc) =
      letterOf h ((β : ℤ) - B.col j.castSucc) := by
  change letterOf h ((β : ℤ) - spliceCol K B (Fin.natAdd k j).castSucc) = _
  rw [spliceCol_bot K B _ (by simp)]
  have e : (⟨(Fin.natAdd k j).castSucc.val - k, by simp⟩ : Fin (b + 1)) = j.castSucc :=
    Fin.ext (by simp)
  rw [e]

/-- The coefficient sequence of `H C_K`. -/
noncomputable def capSeries (w : Fin k → F) : ℕ → F :=
  fun n => PowerSeries.coeff n (PowerSeries.mk h * (capPoly w (leftExp K) : PowerSeries F))

theorem capSeries_mul (w : Fin k → F) (q : F[X]) :
    PowerSeries.mk h * ((capPoly w (leftExp K) * q : F[X]) : PowerSeries F) =
      PowerSeries.mk (capSeries h K w) * (q : PowerSeries F) := by
  rw [Polynomial.coe_mul, ← mul_assoc]
  congr 1
  ext m
  simp [capSeries]

/-- A top-row combination at an arbitrary label `x` is a letter of `H C_K`. -/
theorem topComboAt_eq (w : Fin k → F) (x : ℤ) (hx : 0 ≤ B.row 0 + K.row 0 - x) :
    letterOf h (B.row 0 + K.row 0 - x) +
        ∑ i : Fin k, w i * letterOf h (B.row 0 + K.row i.succ - x) =
      letterOf (capSeries h K w) (B.row 0 + K.row 0 - x) := by
  unfold capSeries
  rw [letterOf_coeff _ hx, coeff_mk_mul_capPoly, letterOf_nonneg_eq h hx]
  have hnat : (((B.row 0 + K.row 0 - x).toNat : ℕ) : ℤ) = B.row 0 + K.row 0 - x :=
    Int.toNat_of_nonneg hx
  rw [hnat]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [leftExp_cast]
  congr 2
  ring

/-- **The differentiated fixed-cap identity** (`sc:splice-identity` differentiated): for normalized
`K`, `B` and a vacancy `β` of `B` below its top, the bordered derivative of the splice is
`κ_K (κ̇_B [H C_K G_B]_{c+a} + κ_B [H C_K δ^{(β)}]_{c+a})`. -/
theorem splice_restorationPoly_eq (hKu : (properMatrixOf h K).det ≠ 0)
    (hBt : (properMatrixOf h B).det ≠ 0) (β : ℕ) (hβ : (β : ℤ) < B.row 0) :
    restorationPoly h (splice K B hK hB) β = cornerOf h K * (cornerDot h B β *
      PowerSeries.coeff (span B + span K) (PowerSeries.mk h *
        ((leftCoframeOf h K * coframeOf h B : F[X]) : PowerSeries F)) + cornerOf h B *
      PowerSeries.coeff (span B + span K) (PowerSeries.mk h *
        ((leftCoframeOf h K * pulse h (rowPos B) (colPos B) (PowerSeries.coeff β
          (PowerSeries.mk h * (coframeOf h B : PowerSeries F))) β : F[X]) : PowerSeries F))) := by
  classical
  have hKu' : IsUnit (properMatrixOf h K).det := isUnit_iff_ne_zero.mpr hKu
  have hBu' : IsUnit (properMatrixOf h B).det := isUnit_iff_ne_zero.mpr hBt
  have hB0 : B.col (Fin.last b) = 0 := hB
  have hK0 : K.col (Fin.last k) = 0 := hK
  have hD0 : (splice K B hK hB).col (Fin.last (k + b)) = 0 := splice_norm K B hK hB
  have hKtop := top_pos K hK
  have hBtop := top_pos B hB
  set TK := properMatrixOf h K with hTK
  set TB := properMatrixOf h B with hTB
  set X := crossBlock h K B with hX
  set w := leftVecOf h K with hw
  set gB := coframeVecOf h B with hgBdef
  set vB : Fin b → F := fun i => letterOf h (B.row i.succ - β) with hvB
  set yB : Fin b → F := TB⁻¹ *ᵥ vB with hyBdef
  set rK : Fin k → F := fun i => (X *ᵥ gB) i + capEntry h K B i.succ (Fin.last b) with hrK
  set sK : Fin k → F := fun i => letterOf h (B.row 0 + K.row i.succ - β) with hsK
  set gK : Fin k → F := -(TK⁻¹ *ᵥ rK) with hgK
  set yK : Fin k → F := TK⁻¹ *ᵥ (sK - X *ᵥ yB) with hyK
  have hgB : TB *ᵥ gB = -topVecOf h B := properMatrix_mulVec_coframeVecOf h B hBt
  have hyB : TB *ᵥ yB = vB := by
    rw [hyBdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hBu', Matrix.one_mulVec]
  have hgKs : TK *ᵥ gK = -rK := by
    rw [hgK, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hKu',
      Matrix.one_mulVec]
  have hyKs : TK *ᵥ yK = sK - X *ᵥ yB := by
    rw [hyK, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hKu', Matrix.one_mulVec]
  have hg' : properMatrixOf h (splice K B hK hB) *ᵥ (Fin.append gK gB : Fin (k + b) → F) =
      -topVecOf h (splice K B hK hB) := by
    ext i
    induction i using Fin.addCases with
    | left i =>
      rw [sp_mulVec_left h K B hK hB, ← hX, Pi.neg_apply, sp_f_top h K B hK hB, hgKs]
      simp [hrK]
    | right i =>
      rw [sp_mulVec_right h K B hK hB, Pi.neg_apply, sp_f_bot h K B hK hB, hgB]
      rfl
  have hy' : properMatrixOf h (splice K B hK hB) *ᵥ (Fin.append yK yB : Fin (k + b) → F) =
      fun i => letterOf h ((splice K B hK hB).row i.succ - β) := by
    ext i
    induction i using Fin.addCases with
    | left i =>
      rw [sp_mulVec_left h K B hK hB, ← hX, sp_vac_top h K B hK hB, hyKs]
      simp [hsK]
    | right i =>
      rw [sp_mulVec_right h K B hK hB, sp_vac_bot h K B hK hB, hyB]
  rw [restorationPoly_cramer h _ β _ _ hg' hy', sp_corner h K B hK hB]
  have hNz : ((span B + span K : ℕ) : ℤ) = B.row 0 + K.row 0 := by
    rw [span_eq_of_norm B hB, span_eq_of_norm K hK]
    push_cast
    rw [Int.toNat_of_nonneg hBtop.le, Int.toNat_of_nonneg hKtop.le]
  -- the vacancy row against the solutions
  have hP1 : (fun j : Fin (k + b) => letterOf h ((β : ℤ) -
      (splice K B hK hB).col j.castSucc)) ⬝ᵥ (Fin.append yK yB : Fin (k + b) → F) =
      (fun j : Fin b => letterOf h ((β : ℤ) - B.col j.castSucc)) ⬝ᵥ yB := by
    simp only [dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      sp_row_top h K B hK hB β hβ, sp_row_bot h K B hK hB β, zero_mul, Finset.sum_const_zero,
      zero_add]
  have hP2 : letterOf h ((β : ℤ) - (splice K B hK hB).col (Fin.last (k + b))) +
      (fun j : Fin (k + b) => letterOf h ((β : ℤ) - (splice K B hK hB).col j.castSucc)) ⬝ᵥ
        (Fin.append gK gB : Fin (k + b) → F) =
      PowerSeries.coeff β (PowerSeries.mk h * (coframeOf h B : PowerSeries F)) := by
    rw [coeff_coframe_vac h B hB β, hD0, hB0]
    congr 1
    simp only [dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      sp_row_top h K B hK hB β hβ, sp_row_bot h K B hK hB β, zero_mul, Finset.sum_const_zero,
      zero_add]
    rfl
  have hcd := cornerDot_eq h B β yB hyB
  -- the top row against the solutions
  have htopg : (fun j : Fin (k + b) => letterOf h ((splice K B hK hB).row 0 -
      (splice K B hK hB).col j.castSucc)) ⬝ᵥ (Fin.append gK gB : Fin (k + b) → F) =
      topRowOf h K ⬝ᵥ gK + (fun j : Fin b => capEntry h K B 0 j.castSucc) ⬝ᵥ gB := by
    simp only [dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      sp_top_tl h K B hK hB, sp_top_tr h K B hK hB]
  have htopy : (fun j : Fin (k + b) => letterOf h ((splice K B hK hB).row 0 -
      (splice K B hK hB).col j.castSucc)) ⬝ᵥ (Fin.append yK yB : Fin (k + b) → F) =
      topRowOf h K ⬝ᵥ yK + (fun j : Fin b => capEntry h K B 0 j.castSucc) ⬝ᵥ yB := by
    simp only [dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      sp_top_tl h K B hK hB, sp_top_tr h K B hK hB]
  have htopK : topRowOf h K ⬝ᵥ gK = w ⬝ᵥ rK := by
    rw [hgK, dotProduct_neg, Matrix.dotProduct_mulVec, hw]
    unfold leftVecOf
    rw [neg_dotProduct]
  have htopKy : topRowOf h K ⬝ᵥ yK = -(w ⬝ᵥ (sK - X *ᵥ yB)) := by
    rw [hyK, Matrix.dotProduct_mulVec, hw]
    unfold leftVecOf
    rw [neg_dotProduct, neg_neg]
  have hsw : ∑ i : Fin k, w i * (X *ᵥ gB) i = ∑ j : Fin b,
      (∑ i : Fin k, w i * capEntry h K B i.succ j.castSucc) * gB j := by
    calc ∑ i : Fin k, w i * (X *ᵥ gB) i
        = ∑ i : Fin k, ∑ j : Fin b, w i * (capEntry h K B i.succ j.castSucc * gB j) := by
          simp [Matrix.mulVec, dotProduct, Finset.mul_sum, hX, crossBlock]
      _ = ∑ j : Fin b, ∑ i : Fin k, w i * (capEntry h K B i.succ j.castSucc * gB j) :=
          Finset.sum_comm
      _ = _ := by simp [Finset.sum_mul, mul_assoc]
  have hswy : ∑ i : Fin k, w i * (X *ᵥ yB) i = ∑ j : Fin b,
      (∑ i : Fin k, w i * capEntry h K B i.succ j.castSucc) * yB j := by
    calc ∑ i : Fin k, w i * (X *ᵥ yB) i
        = ∑ i : Fin k, ∑ j : Fin b, w i * (capEntry h K B i.succ j.castSucc * yB j) := by
          simp [Matrix.mulVec, dotProduct, Finset.mul_sum, hX, crossBlock]
      _ = ∑ j : Fin b, ∑ i : Fin k, w i * (capEntry h K B i.succ j.castSucc * yB j) :=
          Finset.sum_comm
      _ = _ := by simp [Finset.sum_mul, mul_assoc]
  have hE1 : letterOf h ((splice K B hK hB).row 0 - (splice K B hK hB).col (Fin.last (k + b))) +
      (fun j : Fin (k + b) => letterOf h ((splice K B hK hB).row 0 -
        (splice K B hK hB).col j.castSucc)) ⬝ᵥ (Fin.append gK gB : Fin (k + b) → F) =
      topCombo h K B w (Fin.last b) + ∑ j : Fin b, topCombo h K B w j.castSucc * gB j := by
    rw [sp_top_last h K B hK hB, htopg, htopK]
    have e1 : ∑ i : Fin k, w i * rK i = ∑ i : Fin k, w i * (X *ᵥ gB) i +
        ∑ i : Fin k, w i * capEntry h K B i.succ (Fin.last b) := by
      simp only [hrK, mul_add, Finset.sum_add_distrib]
    have e2 : ∑ j : Fin b, topCombo h K B w j.castSucc * gB j =
        ∑ j : Fin b, capEntry h K B 0 j.castSucc * gB j + ∑ j : Fin b,
          (∑ i : Fin k, w i * capEntry h K B i.succ j.castSucc) * gB j := by
      simp only [topCombo, add_mul, Finset.sum_add_distrib]
    simp only [dotProduct] at e1 ⊢
    rw [e1, e2, hsw]
    simp only [topCombo]
    ring
  have hP4 : letterOf h ((splice K B hK hB).row 0 - β) - (fun j : Fin (k + b) =>
      letterOf h ((splice K B hK hB).row 0 - (splice K B hK hB).col j.castSucc)) ⬝ᵥ
        (Fin.append yK yB : Fin (k + b) → F) =
      letterOf h (B.row 0 + K.row 0 - β) + ∑ i : Fin k, w i * sK i -
        ∑ j : Fin b, topCombo h K B w j.castSucc * yB j := by
    rw [sp_vac_zero h K B hK hB, htopy, htopKy]
    have e2 : ∑ j : Fin b, topCombo h K B w j.castSucc * yB j =
        ∑ j : Fin b, capEntry h K B 0 j.castSucc * yB j + ∑ j : Fin b,
          (∑ i : Fin k, w i * capEntry h K B i.succ j.castSucc) * yB j := by
      simp only [topCombo, add_mul, Finset.sum_add_distrib]
    have e3 : w ⬝ᵥ (sK - X *ᵥ yB) = ∑ i : Fin k, w i * sK i - ∑ i : Fin k, w i * (X *ᵥ yB) i := by
      simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [e2, e3, hswy]
    simp only [dotProduct]
    ring
  have hx : 0 ≤ B.row 0 + K.row 0 - (β : ℤ) := by omega
  have hl : topCombo h K B w (Fin.last b) = capSeries h K w (span B + span K) := by
    rw [topCombo_eq hK hB w, hB0, sub_zero, ← hNz, letterOf_natCast]
    rfl
  have hlj : ∀ j : Fin b, topCombo h K B w j.castSucc =
      letterOf (capSeries h K w) (((span B + span K : ℕ) : ℤ) - colPos B j) := fun j => by
    rw [topCombo_eq hK hB w, hNz, colPos_cast_of_norm hB j]
    rfl
  have hQ1 : PowerSeries.coeff (span B + span K) (PowerSeries.mk h *
      ((leftCoframeOf h K * coframeOf h B : F[X]) : PowerSeries F)) =
      topCombo h K B w (Fin.last b) + ∑ j : Fin b, topCombo h K B w j.castSucc * gB j := by
    have e : leftCoframeOf h K * coframeOf h B = capPoly w (leftExp K) * capPoly gB (colPos B) :=
      rfl
    rw [e, capSeries_mul, coeff_mk_mul_capPoly, hl]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlj j, mul_comm]
  have hQ2 : PowerSeries.coeff (span B + span K) (PowerSeries.mk h *
      ((leftCoframeOf h K * pulse h (rowPos B) (colPos B) (PowerSeries.coeff β
        (PowerSeries.mk h * (coframeOf h B : PowerSeries F))) β : F[X]) : PowerSeries F)) =
      -(PowerSeries.coeff β (PowerSeries.mk h * (coframeOf h B : PowerSeries F))) *
        (letterOf (capSeries h K w) (B.row 0 + K.row 0 - β) -
          ∑ j : Fin b, topCombo h K B w j.castSucc * yB j) := by
    have e : leftCoframeOf h K * pulse h (rowPos B) (colPos B) (PowerSeries.coeff β
        (PowerSeries.mk h * (coframeOf h B : PowerSeries F))) β =
        capPoly w (leftExp K) * pulse h (rowPos B) (colPos B) (PowerSeries.coeff β
        (PowerSeries.mk h * (coframeOf h B : PowerSeries F))) β := rfl
    rw [e, capSeries_mul, coeff_series_mul_pulse', properMat_eq, vacancyVec_eq h B hB β, hNz]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlj j, hNz, mul_comm]
  have hAtop : letterOf h (B.row 0 + K.row 0 - β) + ∑ i : Fin k, w i * sK i =
      letterOf (capSeries h K w) (B.row 0 + K.row 0 - β) :=
    topComboAt_eq h K B w (β : ℤ) hx
  rw [hP1, hP2, hE1, hP4, hQ1, hQ2, hcd, hAtop]
  ring

/-- The weighted differentiated fixed-cap identity: with the first variation
`Q = ∑_β ρ_β δ^{(β)}` of the coframe of `B`,
`∑_β ρ_β ṡ^{(β)}_{K ◁ B} = κ_K (κ̇_B [H C_K G_B]_{c+a} + κ_B [H C_K Q]_{c+a})`. -/
theorem splice_restorationSum_eq {m : ℕ} (hKu : (properMatrixOf h K).det ≠ 0)
    (hBt : (properMatrixOf h B).det ≠ 0) (bpos : Fin m → ℕ)
    (hbpos : ∀ v, ((bpos v : ℕ) : ℤ) < B.row 0) (ρ : Fin m → F) :
    ∑ v, ρ v * restorationPoly h (splice K B hK hB) (bpos v) = cornerOf h K *
      ((∑ v, ρ v * cornerDot h B (bpos v)) *
        PowerSeries.coeff (span B + span K) (PowerSeries.mk h *
          ((leftCoframeOf h K * coframeOf h B : F[X]) : PowerSeries F)) + cornerOf h B *
        PowerSeries.coeff (span B + span K) (PowerSeries.mk h *
          ((leftCoframeOf h K * pulseSum h (rowPos B) (colPos B) bpos (fun v =>
            PowerSeries.coeff (bpos v) (PowerSeries.mk h * (coframeOf h B : PowerSeries F))) ρ :
            F[X]) : PowerSeries F))) := by
  have hlin : PowerSeries.coeff (span B + span K) (PowerSeries.mk h *
      ((leftCoframeOf h K * pulseSum h (rowPos B) (colPos B) bpos (fun v =>
        PowerSeries.coeff (bpos v) (PowerSeries.mk h * (coframeOf h B : PowerSeries F))) ρ :
        F[X]) : PowerSeries F)) =
      ∑ v, ρ v * PowerSeries.coeff (span B + span K) (PowerSeries.mk h *
        ((leftCoframeOf h K * pulse h (rowPos B) (colPos B) (PowerSeries.coeff (bpos v)
          (PowerSeries.mk h * (coframeOf h B : PowerSeries F))) (bpos v) : F[X]) :
          PowerSeries F)) := by
    unfold pulseSum
    rw [Finset.mul_sum]
    rw [show (((∑ v, leftCoframeOf h K * (Polynomial.C (ρ v) * pulse h (rowPos B) (colPos B) _
        (bpos v))) : F[X]) : PowerSeries F) = ∑ v, ((leftCoframeOf h K *
        (Polynomial.C (ρ v) * pulse h (rowPos B) (colPos B) _ (bpos v)) : F[X]) : PowerSeries F)
      from map_sum (Polynomial.coeToPowerSeries.ringHom (R := F)) _ _, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_left_comm (leftCoframeOf h K), Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm,
      PowerSeries.coeff_C_mul]
  have hv : ∀ v, ρ v * restorationPoly h (splice K B hK hB) (bpos v) = cornerOf h K *
      (ρ v * cornerDot h B (bpos v) * PowerSeries.coeff (span B + span K) (PowerSeries.mk h *
          ((leftCoframeOf h K * coframeOf h B : F[X]) : PowerSeries F)) + cornerOf h B *
        (ρ v * PowerSeries.coeff (span B + span K) (PowerSeries.mk h *
        ((leftCoframeOf h K * pulse h (rowPos B) (colPos B) (PowerSeries.coeff (bpos v)
          (PowerSeries.mk h * (coframeOf h B : PowerSeries F))) (bpos v) : F[X]) :
          PowerSeries F)))) := fun v => by
    rw [splice_restorationPoly_eq h K B hK hB hKu hBt (bpos v) (hbpos v)]
    ring
  rw [hlin]
  simp only [hv, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]

end SpliceEntries

end SkewCoframeRigidity.UnitRestoration

