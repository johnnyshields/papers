/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.InteriorCofactor
import SkewGluing.IntegralSchur

/-!
# Integral corner expansion

Formalizes `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `lem:cofactor`). Expanding the first determinant row supplies an integral
remainder supported strictly below the top generator. The complementary integral determinant
is the product over the actual southeast interior components. Sorry-free.
-/

namespace SkewGluing
open MvPolynomial
noncomputable section

/-- The integral positive-index entry is the corresponding generator. -/
theorem integralHH_pnat (k : ℕ+) : integralHH (k : ℤ) = X k := by
  simp only [integralHH, Int.natCast_nonneg, not_lt.mpr, ite_false, Int.toNat_natCast,
    hExp, k.pos, dite_true]
  rfl

/-- An integral entry of lower index uses only generators below the given bound. -/
theorem integralHH_mem_below {x : ℤ} {L : ℕ+} (hx : x < (L : ℤ)) :
    integralHH x ∈ supported ℤ {k : ℕ+ | k < L} := by
  by_cases hn : x < 0
  · simp only [integralHH, hn, ite_true]
    exact Subalgebra.zero_mem _
  · by_cases hz : x = 0
    · subst x
      simp [integralHH, hExp]
    · have hp : 0 < x := by omega
      let k : ℕ+ := ⟨x.toNat, by omega⟩
      have he : integralHH x = X k := by
        convert integralHH_pnat k using 1
        congr 1
        change x = (x.toNat : ℤ)
        omega
      rw [he, X_mem_supported]
      change x.toNat < (L : ℕ)
      omega

private theorem integral_det_mem (S : Subalgebra ℤ (MvPolynomial ℕ+ ℤ))
    {k : ℕ} (A : Matrix (Fin k) (Fin k) (MvPolynomial ℕ+ ℤ))
    (hA : ∀ i j, A i j ∈ S) : A.det ∈ S := by
  rw [Matrix.det_apply']
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _
    (Subalgebra.intCast_mem _ _) ?_
  exact Subalgebra.prod_mem _ fun i _ => hA _ _

namespace Profile
variable {n : ℕ}

/-- The complementary integral determinant is the actual interior-component product. -/
theorem integralMinorDet_eq_interiorSchur (P : Profile n) :
    integralBetaDet (fun i : Fin n => P.xi i.succ) (fun i : Fin n => P.zeta i.castSucc) =
      integralCellSchur (diagramInterior P.cells) P.isSkew_cells.interior := by
  apply map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
  simpa only [map_integralBetaDet, map_integralCellSchur] using P.minorDet_eq_interiorSchur

/-- Every interior generator lies strictly below the parent profile's top generator. -/
theorem integralInterior_mem_below (P : Profile n) :
    integralCellSchur (diagramInterior P.cells) P.isSkew_cells.interior ∈
      supported ℤ {k : ℕ+ | k < P.topVar} := by
  rw [← P.integralMinorDet_eq_interiorSchur]
  apply integral_det_mem
  intro i j
  apply integralHH_mem_below
  change P.xi i.succ - P.zeta j.castSucc < (P.topVar : ℤ)
  have hx := P.xi_strictAnti (Fin.succ_pos i)
  have hz := P.zeta_nonneg j.castSucc
  rw [P.topVar_coe]
  omega

/-- The integral corner expansion, with every remainder generator strictly below the top. -/
theorem integralSchur_corner (P : Profile n) :
    ∃ R ∈ supported ℤ {k : ℕ+ | k < P.topVar},
      P.integralSchur = (-1) ^ n * X P.topVar *
        integralCellSchur (diagramInterior P.cells) P.isSkew_cells.interior + R := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial ℕ+ ℤ) :=
    Matrix.of fun i j => integralHH (P.xi i - P.zeta j)
  have hentry : ∀ i j, i ≠ 0 ∨ j ≠ Fin.last n →
      A i j ∈ supported ℤ {k : ℕ+ | k < P.topVar} := by
    intro i j hij
    apply integralHH_mem_below
    have hle := P.xi_sub_zeta_le i j
    have hne : P.xi i - P.zeta j ≠ P.xi 0 := by
      intro he
      obtain ⟨hi, hj⟩ := P.xi_sub_zeta_eq_top he
      rcases hij with h | h
      · exact h hi
      · exact h hj
    rw [P.topVar_coe]
    omega
  refine ⟨∑ j : Fin n, (-1) ^ (j.castSucc : ℕ) * A 0 j.castSucc *
    (A.submatrix Fin.succ j.castSucc.succAbove).det, ?_, ?_⟩
  · refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ ?_ ?_) ?_
    · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _
    · exact hentry _ _ (Or.inr (Fin.castSucc_lt_last j).ne)
    · exact integral_det_mem _ _ fun i i' => hentry _ _ (Or.inl (Fin.succ_ne_zero i))
  · change A.det = _
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_castSucc]
    have htop : A 0 (Fin.last n) = X P.topVar := by
      change integralHH (P.xi 0 - P.zeta (Fin.last n)) = _
      rw [P.zeta_last, sub_zero, ← P.topVar_coe, integralHH_pnat]
    have hminor : (A.submatrix Fin.succ (Fin.last n).succAbove).det =
        integralCellSchur (diagramInterior P.cells) P.isSkew_cells.interior := by
      rw [Fin.succAbove_last]
      exact P.integralMinorDet_eq_interiorSchur
    rw [htop, hminor, Fin.val_last]
    ring

/-- The rational corner remainder is the image of an integral lower-generator polynomial. -/
theorem schur_corner_integralRemainder (P : Profile n) :
    ∃ R ∈ supported ℤ {k : ℕ+ | k < P.topVar},
      P.schur = (-1) ^ n * X P.topVar *
        cellSchur (diagramInterior P.cells) P.isSkew_cells.interior +
          map (Int.castRingHom ℚ) R := by
  obtain ⟨R, hR, he⟩ := P.integralSchur_corner
  refine ⟨R, hR, ?_⟩
  have h := congrArg (map (Int.castRingHom ℚ)) he
  simpa only [map_integralSchur, map_add, map_mul, map_pow, map_neg, map_one, map_X,
    map_integralCellSchur] using h

end Profile
end
end SkewGluing
