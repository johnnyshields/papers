/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalSignedFactors
import SkewCornerDescent.Matrix.OriginalPolynomialFamilies

/-!
# True-cap normalization of original response products

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). The internal family is extracted from the
actual ordered original matrix. Both exterior responses remain explicit. Identifying the
caps of two literal full-window profiles is a separate geometric obligation. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Split both exterior occurrences from a finite ordered product, including a one-block source. -/
theorem prod_two_caps_internal {R : Type*} [CommMonoid R] {B : ℕ} (hB : 0 < B)
    (f : Fin (B + 1) → R) :
    ∏ i, f i = f 0 * f (Fin.last B) *
      ∏ i : Fin (B - 1), f ⟨i.val + 1, by omega⟩ := by
  cases B with
  | zero => omega
  | succ m =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
    simp only [Fin.succ_last]
    have he : (fun i : Fin m => f i.castSucc.succ) =
        (fun i : Fin m => f ⟨i.val + 1, by omega⟩) := rfl
    rw [he]
    ac_rfl

namespace SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The product of the two actual exterior retained responses. Equal caps are counted twice. -/
noncomputable def originalTrueCapProduct {n : ℕ} (P : Profile n) : OtherField c.top :=
  c.regularResidue (c.originalHessenbergResponse P 0 0) *
    c.regularResidue (c.originalHessenbergResponse P (Fin.last _) (Fin.last _))

/-- The actual internal retained responses, with the original ordering and multiplicities. -/
noncomputable def originalInternalResidue {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) : OtherField c.top :=
  c.regularResidue (c.originalHessenbergResponse P
    ⟨i.val + 1, by omega⟩ ⟨i.val + 1, by omega⟩)

/-- The true exterior pair and every internal original occurrence exhaust the full product. -/
theorem originalHessenberg_residue_cap_product {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    (∏ i, c.regularResidue (c.originalHessenbergResponse P i i)) =
      c.originalTrueCapProduct P * ∏ i, c.originalInternalResidue P i :=
  prod_two_caps_internal hB _

/-- Every internal polynomial is produced from its actual original response, not chosen as an
independent variable or supplied as a matching family. The literal top is retained. -/
theorem originalInternal_polynomial_family {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ J : Fin (originalSelectedCount (hD := hD) P - 1) → ResidueHigherIndex c.top,
      ∃ B : Fin (originalSelectedCount (hD := hD) P - 1) → ResidueHigherPolynomial c.top,
        ∀ i, (∀ j ∈ (B i).vars, j < J i) ∧
          residueHigherEval c.top (X (J i) + B i) = c.originalInternalResidue P i ∧
          ((J i).val : ℤ) = originalHessenbergDistance (hD := hD) P
            ⟨i.val + 1, by omega⟩ ⟨i.val + 1, by omega⟩ := by
  obtain ⟨J, B, hf⟩ := c.originalHessenberg_polynomial_family P hB hmax
  exact ⟨fun i => J ⟨i.val + 1, by omega⟩,
    fun i => B ⟨i.val + 1, by omega⟩, fun i => hf ⟨i.val + 1, by omega⟩⟩

/-- Every diagonal response is nonzero in the actual residue field. -/
theorem originalHessenberg_residue_ne_zero {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (i : Fin (originalSelectedCount (hD := hD) P + 1)) :
    c.regularResidue (c.originalHessenbergResponse P i i) ≠ 0 := by
  obtain ⟨J, B, hf⟩ := c.originalHessenberg_polynomial_family P hB hmax
  intro hz
  apply (monicTriangularPolynomial_prime (hf i).1).ne_zero
  apply residueHigherEval_injective c.top
  simpa only [(hf i).2.1, map_zero] using hz

/-- The exterior product never vanishes, including when its two factors coincide. -/
theorem originalTrueCapProduct_ne_zero {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    c.originalTrueCapProduct P ≠ 0 :=
  mul_ne_zero (c.originalHessenberg_residue_ne_zero P hB hmax 0)
    (c.originalHessenberg_residue_ne_zero P hB hmax (Fin.last _))

/-- Original corner cancellation produces the exact signed internal response equation.
The common-cap premise is DERIVED: its producer must identify the actual full-window endpoint
intervals. Neither the signed scalar nor either parent response factorization is assumed. -/
theorem originalHessenberg_cap_normalized_ratio {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hBP : 0 < originalSelectedCount (hD := hD) P)
    (hBQ : 0 < originalSelectedCount (hD := hD) Q)
    (hP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ))
    (b v d : ℕ) (hd : d + v = b)
    (hcorner : (jtMatrix (fun j : Fin n => P.xi j.succ)
          (fun j => P.zeta j.castSucc)).det ^ v =
      (jtMatrix (fun j : Fin m => Q.xi j.succ)
          (fun j => Q.zeta j.castSucc)).det ^ b)
    (hcaps : c.originalTrueCapProduct P = c.originalTrueCapProduct Q) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      c.residueMap P.schur ^ v / c.residueMap Q.schur ^ b =
        (ε : OtherField c.top) * (∏ i, c.originalInternalResidue P i) ^ v /
          ((∏ i, c.originalInternalResidue Q i) ^ b * c.originalTrueCapProduct P ^ d) := by
  obtain ⟨aP, aQ, ε, hε, _, haQ, hfP, hfQ, ha⟩ :=
    c.originalHessenberg_residue_pair_normalization P Q hP hQ b v hcorner
  have hF := c.originalTrueCapProduct_ne_zero P hBP hP
  have hW : (∏ i, c.originalInternalResidue Q i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact c.originalHessenberg_residue_ne_zero Q hBQ hQ ⟨i.val + 1, by omega⟩
  have haQ' : (aQ : OtherField c.top) ≠ 0 := by
    exact_mod_cast haQ
  have hscalar := congrArg
    (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) ha
  change (aP : OtherField c.top) ^ v / (aQ : OtherField c.top) ^ b =
    (ε : OtherField c.top) at hscalar
  have hscalar' := (div_eq_iff (pow_ne_zero b haQ')).mp hscalar
  refine ⟨ε, hε, ?_⟩
  rw [hfP, hfQ, c.originalHessenberg_residue_cap_product P hBP,
    c.originalHessenberg_residue_cap_product Q hBQ, ← hcaps, mul_pow, mul_pow,
    mul_pow, mul_pow, hscalar']
  have hb : b = d + v := hd.symm
  rw [hb, pow_add]
  field_simp
  ring

end SelectedCoordinate
end SkewCornerDescent.Matrix
