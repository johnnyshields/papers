/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.WholeUnit
import SkewCoframeRigidity.UnitRestoration.UnitCore
import SkewCoframeRigidity.UnitRestoration.StrictBlock

/-!
# Grades of a Schur polynomial and the whole-unit expansion

`epsHom` scales every positive complete generator by `ε = X`, so that the coefficient of `ε^g`
of `epsHom p` is the component of `p` of degree `g` in the positive letters
(`coeff_epsHom`).  For an actual diagram `D` with `k` core rows and sorting sign `σ`,
`sc:whole-unit-series` reads
`epsHom s_D = σ ε^k (s_{D₀} - ε T_D + O(ε²))`
(`epsHom_schur_expansion`), the first order term being `T_D = tr (F adj(K) G)`.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence MvPolynomial Polynomial

local notation "CR" => SkewCofactorIndependence.CompleteRing

/-- Scale every positive complete generator by `ε = X`; the unit stays one. -/
noncomputable def epsHom : CR →ₐ[ℚ] CR[X] :=
  MvPolynomial.aeval fun i : ℕ+ => (Polynomial.C (MvPolynomial.X i : CR) * Polynomial.X)

theorem epsHom_monomial (d : ℕ+ →₀ ℕ) (a : ℚ) :
    epsHom (monomial d a) =
      Polynomial.C (monomial d a : CR) * Polynomial.X ^ (d.sum fun _ k => k) := by
  rw [epsHom, MvPolynomial.aeval_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    Finset.prod_pow_eq_pow_sum, Finsupp.sum]
  rw [monomial_eq]
  have : (algebraMap ℚ CR[X]) a = Polynomial.C (MvPolynomial.C a : CR) := rfl
  rw [this]
  simp only [map_mul, Finsupp.prod]
  ring

theorem coeff_epsHom (p : CR) (g : ℕ) :
    (epsHom p).coeff g = homogeneousComponent g p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    have hd : (d.sum fun _ k => k) = d.degree := by
      rw [Finsupp.degree_apply]; rfl
    rw [epsHom_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hd,
      homogeneousComponent_of_mem (m := g) (n := d.degree) (isHomogeneous_monomial a rfl)]
    by_cases h : d.degree = g
    · simp [h]
    · simp [Ne.symm h]
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, map_add]

open scoped Classical

/-- The letters of the complete ring as a sequence, `h_0 = 1`. -/
noncomputable def letterSeq : ℕ → CR := fun m => complete (m : ℤ)

theorem letterOf_letterSeq (k : ℤ) : SkewCoframeRigidity.Coframe.letterOf letterSeq k = complete k := by
  unfold SkewCoframeRigidity.Coframe.letterOf
  split_ifs with h
  · exact (complete_of_neg h).symm
  · simp [letterSeq, Int.toNat_of_nonneg (not_lt.mp h)]

theorem epsHom_complete (k : ℤ) : epsHom (complete k) = scaledLetter letterSeq k := by
  unfold scaledLetter
  split_ifs with h1 h2
  · rw [complete_of_neg h1, map_zero]
  · subst h2; simp
  · have hk : 0 < k := by omega
    have hx : letterSeq k.toNat = MvPolynomial.X (⟨k.toNat, by omega⟩ : ℕ+) := by
      simp only [letterSeq, Int.toNat_of_nonneg hk.le]; exact complete_of_pos hk
    rw [complete_of_pos hk, hx]
    exact MvPolynomial.aeval_X (R := ℚ) _ (⟨k.toNat, by omega⟩ : ℕ+)

theorem epsHom_schur {m : ℕ} (D : BetaDiagram m) :
    epsHom D.schur = (scaledMatrix letterSeq D.row D.col).det := by
  unfold BetaDiagram.schur
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [BetaDiagram.matrix, scaledMatrix, epsHom_complete]

/-- The field of fractions of the complete ring, where the whole-unit series is computed. -/
abbrev FF : Type := FractionRing CR

/-- The letters in the field of fractions. -/
noncomputable def letterSeqF : ℕ → FF := fun m => algebraMap CR FF (letterSeq m)

theorem algebraMap_injective_FF : Function.Injective (algebraMap CR FF) :=
  IsFractionRing.injective CR FF

theorem scaledLetter_map (k : ℤ) :
    scaledLetter letterSeqF k = (scaledLetter letterSeq k).map (algebraMap CR FF) := by
  unfold scaledLetter
  split_ifs <;> simp [letterSeqF]

theorem letterOf_letterSeqF (k : ℤ) :
    SkewCoframeRigidity.Coframe.letterOf letterSeqF k =
      algebraMap CR FF (SkewCoframeRigidity.Coframe.letterOf letterSeq k) := by
  unfold SkewCoframeRigidity.Coframe.letterOf
  split_ifs <;> simp [letterSeqF]

/-- The first-order coefficient of the whole-unit series, `tr (F adj(K) G)`. -/
noncomputable def traceT {m : ℕ} (D : BetaDiagram m) : FF :=
  Matrix.trace (unitF letterSeqF D.row D.col (corePairing D) *
    (coreMatrix letterSeqF D.row D.col (corePairing D)).adjugate *
    unitG letterSeqF D.row D.col (unitPairing D))

theorem card_core_subtype {m : ℕ} (D : BetaDiagram m) :
    Fintype.card {i // i ∉ unitRows D.row D.col} = coreCount D := by
  rw [← card_coreRows_eq_count, coreRows, Fintype.card_subtype]

theorem schurOf_letterSeq {m : ℕ} (D : BetaDiagram m) :
    SkewCoframeRigidity.Coframe.schurOf letterSeqF D = algebraMap CR FF D.schur := by
  unfold SkewCoframeRigidity.Coframe.schurOf BetaDiagram.schur
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [SkewCoframeRigidity.Coframe.fullMatrixOf, BetaDiagram.matrix, letterOf_letterSeqF,
    letterOf_letterSeq]

theorem det_coreMatrix_eq {m : ℕ} (D : BetaDiagram m) :
    (coreMatrix letterSeqF D.row D.col (corePairing D)).det =
      algebraMap CR FF (coreDiagram D).schur := by
  rw [det_coreMatrix_corePairing, schurOf_letterSeq]

theorem coeff_int_mul_X_pow_mul (z : ℤ) (P : FF[X]) (k : ℕ) :
    ((z : FF[X]) * (Polynomial.X ^ k * P)).coeff k = (z : FF) * P.coeff 0 := by
  rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  simp

theorem epsHom_schur_map {m : ℕ} (D : BetaDiagram m) :
    (epsHom D.schur).map (algebraMap CR FF) =
      (scaledMatrix letterSeqF D.row D.col).det := by
  rw [epsHom_schur]
  have h := RingHom.map_det (Polynomial.mapRingHom (algebraMap CR FF))
    (scaledMatrix letterSeq D.row D.col)
  rw [Polynomial.coe_mapRingHom] at h
  rw [h]
  congr 1
  ext i j
  simp [scaledMatrix, scaledLetter_map]

/-- **The whole-unit expansion** (`sc:whole-unit-series`) with the sorting sign explicit:
`s_D = σ ε^k (s_{D₀} - ε T_D + ε² q)` over the field of fractions. -/
theorem eps_expansion {m : ℕ} (D : BetaDiagram m) :
    ∃ q : FF[X], (epsHom D.schur).map (algebraMap CR FF) =
      (((sortingSign D : ℤˣ) : ℤ) : FF[X]) * (Polynomial.X ^ coreCount D *
        (Polynomial.C (algebraMap CR FF (coreDiagram D).schur) -
          Polynomial.C (traceT D) * Polynomial.X + Polynomial.X ^ 2 * q)) := by
  have hr := D.row_strictAnti.injective
  have hc := D.col_strictAnti.injective
  have hK : (coreMatrix letterSeqF D.row D.col (corePairing D)).det ≠ 0 := by
    rw [det_coreMatrix_eq]
    exact (map_ne_zero_iff _ algebraMap_injective_FF).mpr (BetaDiagram.schur_ne_zero _)
  obtain ⟨σ, q, h1⟩ := det_scaledMatrix_series letterSeqF D.row D.col hr hc (unitPairing D)
    (unitPairing_spec D) (corePairing D) hK
  obtain ⟨q2, h2⟩ := det_scaledMatrix_of_equiv letterSeqF D.row D.col hr hc (unitPairing D)
    (unitPairing_spec D) (corePairing D)
  have hsign : ((σ : ℤˣ) : ℤ) = ((sortingSign D : ℤˣ) : ℤ) := by
    have h3 := congrArg (fun p => p.coeff (coreCount D)) (h1.symm.trans h2)
    simp only [card_core_subtype] at h3
    rw [coeff_int_mul_X_pow_mul, coeff_int_mul_X_pow_mul] at h3
    simp [Polynomial.coeff_X_pow] at h3
    exact_mod_cast h3.resolve_right hK
  refine ⟨q, ?_⟩
  rw [epsHom_schur_map, h1, hsign, card_core_subtype, det_coreMatrix_eq]
  rfl

/-- The values of the common betas of a diagram. -/
noncomputable def unitVals {m : ℕ} (D : BetaDiagram m) : Finset ℤ :=
  (Finset.univ.filter fun i => i ∈ unitRows D.row D.col).image D.row

theorem mem_unitVals {m : ℕ} {D : BetaDiagram m} {b : ℤ} :
    b ∈ unitVals D ↔ ∃ i j, D.row i = b ∧ D.col j = b := by
  unfold unitVals
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, unitRows,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, ⟨j, hj⟩, rfl⟩; exact ⟨i, j, rfl, hj.symm⟩
  · rintro ⟨i, j, rfl, hj⟩; exact ⟨i, ⟨j, hj.symm⟩, rfl⟩

/-- Each unit's contribution to the first order term. -/
theorem unit_term {m : ℕ} (D : BetaDiagram m) (u : {i // i ∈ unitRows D.row D.col}) :
    ∑ c, ∑ c', unitF letterSeqF D.row D.col (corePairing D) u c *
        (coreMatrix letterSeqF D.row D.col (corePairing D)).adjugate c c' *
        unitG letterSeqF D.row D.col (unitPairing D) c' u =
      -algebraMap CR FF (dotS (coreDiagram D) (D.row u.1)) := by
  set B := coreDiagram D with hB
  set K := coreMatrix letterSeqF D.row D.col (corePairing D) with hK
  have hcp : ∀ b, (corePairing D (coreRowEquiv D b)).1 = coreColEmb D b := fun b =>
    congrArg Subtype.val (corePairing_coreRowEquiv D b)
  have hKB : K.submatrix (coreRowEquiv D) (coreRowEquiv D) =
      B.matrix.map (algebraMap CR FF) := by
    ext a b
    simp only [Matrix.submatrix_apply, hK, coreMatrix, Matrix.of_apply, Matrix.map_apply,
      BetaDiagram.matrix, hB, coreDiagram_row, coreDiagram_col, hcp b, letterOf_letterSeqF,
      letterOf_letterSeq]
    rfl
  have hadj : K.adjugate.submatrix (coreRowEquiv D) (coreRowEquiv D) =
      (B.matrix.adjugate).map (algebraMap CR FF) := by
    rw [← Matrix.adjugate_submatrix_equiv_self (coreRowEquiv D) K, hKB]
    exact (RingHom.map_adjugate (algebraMap CR FF) B.matrix).symm
  have hF : ∀ l, unitF letterSeqF D.row D.col (corePairing D) u (coreRowEquiv D l) =
      algebraMap CR FF (restoreRow B (D.row u.1) l) := by
    intro l
    simp only [unitF, Matrix.of_apply, hcp l, restoreRow, hB, coreDiagram_col,
      letterOf_letterSeqF, letterOf_letterSeq]
  have hG : ∀ l, unitG letterSeqF D.row D.col (unitPairing D) (coreRowEquiv D l) u =
      algebraMap CR FF (restoreCol B (D.row u.1) l) := by
    intro l
    simp only [unitG, Matrix.of_apply, ← unitPairing_spec D u, restoreCol, hB, coreDiagram_row,
      letterOf_letterSeqF, letterOf_letterSeq]
    rfl
  have e1 : ∀ f : {i // i ∉ unitRows D.row D.col} → FF,
      ∑ c, f c = ∑ l, f (coreRowEquiv D l) := fun f => (Equiv.sum_comp (coreRowEquiv D) f).symm
  have hadj' : ∀ l l', K.adjugate (coreRowEquiv D l) (coreRowEquiv D l') =
      algebraMap CR FF (B.matrix.adjugate l l') := fun l l' =>
    congrFun (congrFun hadj l) l'
  rw [e1]
  refine (Finset.sum_congr rfl fun l _ => e1 _).trans ?_
  simp only [hF, hG, hadj']
  rw [dotS, map_neg, neg_neg]
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, mul_assoc]

/-- **The first-order term** of the whole-unit series is the sum of the bordered derivatives at
the unit positions: `T_D = -∑_b ṡ_{D₀}^{(b)}`. -/
theorem traceT_eq {m : ℕ} (D : BetaDiagram m) :
    traceT D = -algebraMap CR FF (∑ b ∈ unitVals D, dotS (coreDiagram D) b) := by
  have h1 : traceT D = ∑ u : {i // i ∈ unitRows D.row D.col},
      ∑ c, ∑ c', unitF letterSeqF D.row D.col (corePairing D) u c *
        (coreMatrix letterSeqF D.row D.col (corePairing D)).adjugate c c' *
        unitG letterSeqF D.row D.col (unitPairing D) c' u := by
    unfold traceT
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
  rw [h1]
  simp_rw [unit_term]
  rw [Finset.sum_neg_distrib, map_sum, ← Finset.sum_subtype (Finset.univ.filter fun i =>
    i ∈ unitRows D.row D.col) (by simp) (fun i => algebraMap CR FF (dotS (coreDiagram D) (D.row i))),
    unitVals, Finset.sum_image (fun i _ j _ h => D.row_strictAnti.injective h)]

theorem coeff_int_mul_X_pow_mul_add (z : ℤ) (P : FF[X]) (k j : ℕ) :
    ((z : FF[X]) * (Polynomial.X ^ k * P)).coeff (k + j) = (z : FF) * P.coeff j := by
  rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul',
    ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem coeff_int_mul_X_pow_mul_lt (z : ℤ) (P : FF[X]) {k g : ℕ} (h : g < k) :
    ((z : FF[X]) * (Polynomial.X ^ k * P)).coeff g = 0 := by
  rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul',
    ite_eq_right (by omega), mul_zero]

/-- **Grades of a Schur polynomial** (`sc:whole-unit-series`): the components of positive-letter
degree below the number `k` of core rows vanish, the component of degree `k` is `σ s_{D₀}`, and
the component of degree `k + 1` is `σ ∑_b ṡ_{D₀}^{(b)}` over the unit positions. -/
theorem grade_expansion {m : ℕ} (D : BetaDiagram m) :
    (∀ g < coreCount D, MvPolynomial.homogeneousComponent g D.schur = 0) ∧
    MvPolynomial.homogeneousComponent (coreCount D) D.schur =
      (((sortingSign D : ℤˣ) : ℤ) : CR) * (coreDiagram D).schur ∧
    MvPolynomial.homogeneousComponent (coreCount D + 1) D.schur =
      (((sortingSign D : ℤˣ) : ℤ) : CR) * ∑ b ∈ unitVals D, dotS (coreDiagram D) b := by
  obtain ⟨q, hq⟩ := eps_expansion D
  have hcoef : ∀ g, algebraMap CR FF (MvPolynomial.homogeneousComponent g D.schur) =
      ((((sortingSign D : ℤˣ) : ℤ) : FF[X]) * (Polynomial.X ^ coreCount D *
        (Polynomial.C (algebraMap CR FF (coreDiagram D).schur) -
          Polynomial.C (traceT D) * Polynomial.X + Polynomial.X ^ 2 * q))).coeff g := by
    intro g
    rw [← hq, Polynomial.coeff_map, coeff_epsHom]
  have hinj := algebraMap_injective_FF
  refine ⟨fun g hg => ?_, ?_, ?_⟩
  · apply hinj
    rw [hcoef, coeff_int_mul_X_pow_mul_lt _ _ hg, map_zero]
  · apply hinj
    have := coeff_int_mul_X_pow_mul_add (((sortingSign D : ℤˣ) : ℤ)) (Polynomial.C
      (algebraMap CR FF (coreDiagram D).schur) - Polynomial.C (traceT D) * Polynomial.X +
        Polynomial.X ^ 2 * q) (coreCount D) 0
    rw [add_zero] at this
    rw [hcoef, this]
    simp
  · apply hinj
    have := coeff_int_mul_X_pow_mul_add (((sortingSign D : ℤˣ) : ℤ)) (Polynomial.C
      (algebraMap CR FF (coreDiagram D).schur) - Polynomial.C (traceT D) * Polynomial.X +
        Polynomial.X ^ 2 * q) (coreCount D) 1
    rw [hcoef, this, traceT_eq]
    simp [Polynomial.coeff_C, Polynomial.coeff_X_pow_mul']

end SkewCoframeRigidity.UnitRestoration
