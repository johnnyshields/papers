/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.UnitCore
import SkewCoframeRigidity.UnitRestoration.UnitRegularity
import SkewCoframeRigidity.RowDegree

/-!
# Coequal diagrams have equal cores

Formalizes the coequal clause of `sc:unit-expansion` in
`shields-2026-skew-coframe-rigidity.tex`: for diagrams with equal whole skew Schur functions the
numbers of rows agree (`sc:row-degree`), the least nonzero powers of `ε` agree, which gives equal
unit counts, and the core functions and the sorting signs agree.  The signs are fixed by the
square initial form, which is a monomial with coefficient one in positive generators, so it
cannot change sign.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity.Coframe Polynomial

variable {n : ℕ}

/-- The scaling `x_k ↦ ε x_k` of the complete ring into `CompleteRing[ε]`. -/
noncomputable def epsScale : CompleteRing →+* CompleteRing[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    fun k => Polynomial.C (MvPolynomial.X k) * Polynomial.X

theorem epsScale_complete (k : ℤ) :
    epsScale (complete k) = scaledLetter (fun m : ℕ => (complete (m : ℤ) : CompleteRing)) k := by
  unfold scaledLetter
  by_cases h1 : k < 0
  · simp [h1]
  · by_cases h2 : k = 0
    · simp [h2]
    · have hpos : 0 < k := by omega
      rw [if_neg h1, if_neg h2, complete_of_pos hpos]
      have : (complete ((k.toNat : ℕ) : ℤ)) = MvPolynomial.X ⟨k.toNat, by omega⟩ :=
        complete_of_pos (by omega)
      show _ = Polynomial.C (complete ((k.toNat : ℕ) : ℤ)) * Polynomial.X
      rw [this]
      simp only [epsScale, MvPolynomial.coe_eval₂Hom]
      exact MvPolynomial.eval₂_X _ _ _

theorem epsScale_schur (D : BetaDiagram n) :
    epsScale D.schur = (scaledMatrix (fun m : ℕ => (complete (m : ℤ) : CompleteRing))
      D.row D.col).det := by
  unfold BetaDiagram.schur
  rw [RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
  simp [BetaDiagram.matrix, scaledMatrix, epsScale_complete]

theorem schur_eq_schurOf (D : BetaDiagram n) :
    D.schur = schurOf (fun m : ℕ => (complete (m : ℤ) : CompleteRing)) D := by
  unfold BetaDiagram.schur schurOf
  refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
  simp only [BetaDiagram.matrix, fullMatrixOf, Matrix.of_apply, letterOf]
  split_ifs with h
  · exact complete_of_neg h
  · rw [Int.toNat_of_nonneg (by omega)]

theorem coeff_lead_lt {R : Type*} [CommRing R] (σ : ℤ) (c : ℕ) (a : R) (q : R[X]) {i : ℕ}
    (hi : i < c) : ((σ : R[X]) * (X ^ c * (C a + X * q))).coeff i = 0 := by
  have e : (σ : R[X]) * (X ^ c * (C a + X * q)) =
      C ((σ : R) * a) * X ^ c + X ^ (c + 1) * (σ : R[X]) * q := by
    have : (σ : R[X]) = C (σ : R) := by simp
    rw [this]; simp only [map_mul]; ring
  rw [e, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, mul_assoc,
    Polynomial.coeff_X_pow_mul', if_neg (by omega), if_neg (by omega)]
  simp

theorem coeff_lead_eq {R : Type*} [CommRing R] (σ : ℤ) (c : ℕ) (a : R) (q : R[X]) :
    ((σ : R[X]) * (X ^ c * (C a + X * q))).coeff c = (σ : R) * a := by
  have e : (σ : R[X]) * (X ^ c * (C a + X * q)) =
      C ((σ : R) * a) * X ^ c + X ^ (c + 1) * (σ : R[X]) * q := by
    have : (σ : R[X]) = C (σ : R) := by simp
    rw [this]; simp only [map_mul]; ring
  rw [e, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, if_pos rfl, mul_assoc,
    Polynomial.coeff_X_pow_mul', if_neg (by omega), add_zero]

theorem initialForm_neg_eval {p : CompleteRing} (w : ℕ+ → ℝ) :
    Base.initialForm w (-p) = -Base.initialForm w p := by
  unfold Base.initialForm
  have h1 : Base.leastWeight w (-p) = Base.leastWeight w p := by
    unfold Base.leastWeight
    rw [MvPolynomial.support_neg]
  rw [h1, map_neg]

/-- The square initial form of a skew Schur function takes the value one at the all-ones
point, so the function cannot be the negative of another one. -/
theorem eval_one_square_initialForm (D : BetaDiagram n) :
    MvPolynomial.eval (fun _ => (1 : ℚ))
      (Base.initialForm Base.squareWeight.generatorWeight D.schur) = 1 := by
  rw [D.square_initialForm, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  have hp : 0 < D.row i - D.col i := by have := D.row_nonempty i; omega
  rw [complete_of_pos hp]
  exact MvPolynomial.eval_X _

theorem schur_ne_neg {m k : ℕ} {D : BetaDiagram m} {E : BetaDiagram k} : D.schur ≠ -E.schur := by
  intro h
  have h1 := congrArg (fun p => MvPolynomial.eval (fun _ => (1 : ℚ))
    (Base.initialForm Base.squareWeight.generatorWeight p)) h
  simp only [initialForm_neg_eval, map_neg, eval_one_square_initialForm] at h1
  norm_num at h1

open scoped Classical in
/-- The scaled determinant of a diagram, as in `det_scaledMatrix_of_equiv`, with the canonical
sorting sign and the canonical core pairing. -/
theorem scaled_schur_expansion (D : BetaDiagram n) :
    ∃ q : CompleteRing[X], epsScale D.schur =
      ((sortingSign D : ℤ) : CompleteRing[X]) *
        (X ^ coreCount D * (C (coreDiagram D).schur + X * q)) := by
  obtain ⟨q, hq⟩ := det_scaledMatrix_of_equiv (fun m : ℕ => (complete (m : ℤ) : CompleteRing))
    D.row D.col D.row_strictAnti.injective D.col_strictAnti.injective (unitPairing D)
    (unitPairing_spec D) (corePairing D)
  refine ⟨q, ?_⟩
  rw [epsScale_schur, hq, det_coreMatrix_corePairing, ← schur_eq_schurOf]
  have : Fintype.card {i // i ∉ unitRows D.row D.col} = coreCount D := by
    rw [Fintype.card_subtype]; rfl
  rw [this]
  rfl

private theorem int_cast_ne_zero {σ : ℤˣ} : ((σ : ℤ) : CompleteRing) ≠ 0 := by
  rcases Int.units_eq_one_or σ with h | h <;> simp [h]

/-- **Coequal diagrams** (`sc:unit-expansion`, last clause): equal whole functions give equal
numbers of core rows (so equal unit counts), equal sorting signs and equal core functions. -/
theorem coequal_core {D E : BetaDiagram n} (h : D.schur = E.schur) :
    coreCount D = coreCount E ∧ sortingSign D = sortingSign E ∧
      (coreDiagram D).schur = (coreDiagram E).schur := by
  obtain ⟨qD, hD⟩ := scaled_schur_expansion D
  obtain ⟨qE, hE⟩ := scaled_schur_expansion E
  have hP : ((sortingSign D : ℤ) : CompleteRing[X]) *
        (X ^ coreCount D * (C (coreDiagram D).schur + X * qD)) =
      ((sortingSign E : ℤ) : CompleteRing[X]) *
        (X ^ coreCount E * (C (coreDiagram E).schur + X * qE)) := by
    rw [← hD, ← hE, h]
  have hSD := (coreDiagram D).schur_ne_zero
  have hSE := (coreDiagram E).schur_ne_zero
  have hcount : coreCount D = coreCount E := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := congrArg (fun P => P.coeff (coreCount D)) hP
      simp only [coeff_lead_eq, coeff_lead_lt _ _ _ _ hlt] at h1
      exact mul_ne_zero int_cast_ne_zero hSD h1
    · have h1 := congrArg (fun P => P.coeff (coreCount E)) hP
      simp only [coeff_lead_eq, coeff_lead_lt _ _ _ _ hlt] at h1
      exact mul_ne_zero int_cast_ne_zero hSE h1.symm
  refine ⟨hcount, ?_⟩
  have h1 := congrArg (fun P => P.coeff (coreCount D)) hP
  have h2 : (((sortingSign E : ℤ) : CompleteRing[X]) *
      (X ^ coreCount E * (C (coreDiagram E).schur + X * qE))).coeff (coreCount D) =
      ((sortingSign E : ℤ) : CompleteRing) * (coreDiagram E).schur := by
    rw [hcount]; exact coeff_lead_eq _ _ _ _
  simp only [coeff_lead_eq] at h1
  rw [h2] at h1
  rcases Int.units_eq_one_or (sortingSign D) with a | a <;>
    rcases Int.units_eq_one_or (sortingSign E) with b | b
  · rw [a, b] at h1 ⊢
    exact ⟨rfl, by simpa using h1⟩
  · rw [a, b] at h1
    simp at h1
    exact absurd h1 schur_ne_neg
  · rw [a, b] at h1
    simp at h1
    exact absurd h1.symm schur_ne_neg
  · rw [a, b] at h1 ⊢
    exact ⟨rfl, by simpa using h1⟩

/-- Equal whole functions force equal numbers of rows (`sc:row-degree`). -/
theorem rows_eq_of_schur_eq {m : ℕ} {D : BetaDiagram n} {E : BetaDiagram m}
    (h : D.schur = E.schur) : n = m := by
  rw [← SkewCoframeRigidity.BetaDiagram.rowDegree D, ← SkewCoframeRigidity.BetaDiagram.rowDegree E,
    h]

end SkewCoframeRigidity.UnitRestoration
