/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.Incidence
import SkewCoframeRigidity.Stationary.PowerEquation
import SkewCoframeRigidity.Stationary.LowerSeries

/-!
# Derivatives of the clipped operator and of the potential

Formalizes the derivative computations in the proof of `sc:positive-power`.  When the coframes
`G`, `C` do not involve the letter `H_{M-1}`, the derivative of `𝒯_{G,C}(u)` is `𝒯_{G,C}(∂u)`;
with `u = z H^p`, `∂u` has order `M` and is clipped away, and `∂D = -z^{M-1}(C - G)`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial

theorem trunc_X_pow_mul_self {F : Type*} [CommRing F] (M : ℕ) (f : PowerSeries F) :
    PowerSeries.trunc M (PowerSeries.X ^ M * f) = 0 := by
  ext i
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_X_pow_mul']
  split_ifs with h1 h2 <;> simp_all <;> omega

theorem trunc_succ_X_pow_mul {F : Type*} [CommRing F] (m : ℕ) (f : PowerSeries F) :
    PowerSeries.trunc (m + 1) (PowerSeries.X ^ m * f) =
      Polynomial.C (PowerSeries.coeff 0 f) * Polynomial.X ^ m := by
  ext i
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_X_pow_mul', Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  by_cases h : i = m
  · subst h; simp
  · by_cases h2 : i < m + 1
    · have : ¬ m ≤ i := by omega
      simp [h2, this, h]
    · simp [h2, h]

theorem dS_clippedOp (m M : ℕ) (G C : CohField[X]) (u : PowerSeries CohField)
    (hG : dS m (G : PowerSeries CohField) = 0) (hC : dS m (C : PowerSeries CohField) = 0) :
    dS m ((clippedOp M G C u : CohField[X]) : PowerSeries CohField) =
      ((clippedOp M G C (dS m u) : CohField[X]) : PowerSeries CohField) := by
  unfold clippedOp
  simp only [Polynomial.coe_sub, Polynomial.coe_mul]
  rw [dS_sub, dS_mul, dS_mul, dS_trunc, dS_trunc, dS_mul, dS_mul, hG, hC]
  simp only [zero_mul, zero_add, mul_zero, add_zero]

theorem dRaw_rat (m : ℕ) (q : ℚ) : dRaw m (algebraMap ℚ CohField q) = 0 := by
  have h : algebraMap ℚ CohField q = algebraMap CohRing CohField (MvPolynomial.C q) := by
    rw [IsScalarTower.algebraMap_apply ℚ CohRing CohField]; rfl
  rw [h, dRaw_algebraMap]; simp

theorem dS_algebraMap (m : ℕ) (q : ℚ) : dS m (algebraMap ℚ (PowerSeries CohField) q) = 0 := by
  ext i
  rw [coeff_dS, map_zero]
  have : algebraMap ℚ (PowerSeries CohField) q = PowerSeries.C (algebraMap ℚ CohField q) := by
    ext i; simp [PowerSeries.coeff_C, Algebra.algebraMap_eq_smul_one, PowerSeries.coeff_one]
  rw [this, PowerSeries.coeff_C]
  split_ifs
  · exact dRaw_rat m q
  · exact dRaw_zero m

/-- A series whose derivative in `H_m` is divisible by `z^m`. -/
def DivDeriv (m : ℕ) (φ : PowerSeries CohField) : Prop := ∃ ψ, dS m φ = PowerSeries.X ^ m * ψ

theorem DivDeriv.add {m : ℕ} {φ ψ : PowerSeries CohField} (h1 : DivDeriv m φ) (h2 : DivDeriv m ψ) :
    DivDeriv m (φ + ψ) := by
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
  exact ⟨a + b, by rw [dS_add, ha, hb]; ring⟩

theorem DivDeriv.mul {m : ℕ} {φ ψ : PowerSeries CohField} (h1 : DivDeriv m φ) (h2 : DivDeriv m ψ) :
    DivDeriv m (φ * ψ) := by
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
  exact ⟨a * ψ + φ * b, by rw [dS_mul, ha, hb]; ring⟩

theorem divDeriv_algebraMap (m : ℕ) (q : ℚ) : DivDeriv m (algebraMap ℚ (PowerSeries CohField) q) :=
  ⟨0, by rw [dS_algebraMap]; ring⟩

theorem divDeriv_letterSeries (m : ℕ) : DivDeriv m letterSeries :=
  ⟨1, by rw [show dS m letterSeries = _ from dS_mk_letters m]; ring⟩

theorem divDeriv_aeval (m : ℕ) (P : ℚ[X]) :
    DivDeriv m (Polynomial.aeval letterSeries P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial k a =>
    rw [Polynomial.aeval_monomial]
    refine (divDeriv_algebraMap m a).mul ?_
    induction k with
    | zero => exact ⟨0, by simp [dS_one]⟩
    | succ k ih => rw [pow_succ]; exact ih.mul (divDeriv_letterSeries m)

theorem divDeriv_inv (m : ℕ) (f : PowerSeries CohField) (h : DivDeriv m f)
    (h0 : PowerSeries.constantCoeff f ≠ 0) : DivDeriv m f⁻¹ := by
  obtain ⟨a, ha⟩ := h
  refine ⟨-(f⁻¹ * f⁻¹ * a), ?_⟩
  have h1 : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel _ h0
  have h2 := congrArg (dS m) h1
  rw [dS_mul, dS_one, ha] at h2
  have hf : f⁻¹ * f = 1 := by rw [mul_comm]; exact h1
  have h3 : f * dS m f⁻¹ = -(PowerSeries.X ^ m * a * f⁻¹) := by linear_combination h2
  calc dS m f⁻¹ = (f⁻¹ * f) * dS m f⁻¹ := by rw [hf, one_mul]
    _ = f⁻¹ * (f * dS m f⁻¹) := by ring
    _ = _ := by rw [h3]; ring

theorem constantCoeff_aeval_letterSeries (P : ℚ[X]) :
    PowerSeries.constantCoeff (Polynomial.aeval letterSeries P) =
      Polynomial.aeval (cohLetters 0) P := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  rw [constantCoeff_letterSeries]
  rfl

theorem aeval_theta_eq_zero {P : ℚ[X]} (h : Polynomial.aeval (cohLetters 0) P = 0) : P = 0 := by
  have ht := cohLetters_algebraicIndependent.transcendental (0 : ℕ)
  by_contra hP
  exact ht ⟨P, hP, h⟩

theorem aeval_theta_ne_zero {Q : ℚ[X]} (hQ : Q ≠ 0) : Polynomial.aeval (cohLetters 0) Q ≠ 0 :=
  fun h => hQ (aeval_theta_eq_zero h)

theorem natDegree_clippedOp_le (M : ℕ) (G C : CohField[X]) (u : PowerSeries CohField)
    (hG : G.natDegree ≤ M - 1) (hC : C.natDegree ≤ M - 1) (hM : 1 ≤ M) :
    (clippedOp M G C u).natDegree ≤ 2 * M - 2 := by
  have h1 : (PowerSeries.trunc M (u * (C : PowerSeries CohField))).natDegree ≤ M - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [PowerSeries.coeff_trunc, if_neg (by omega)]
  have h2 : (PowerSeries.trunc M (u * (G : PowerSeries CohField))).natDegree ≤ M - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [PowerSeries.coeff_trunc, if_neg (by omega)]
  unfold clippedOp
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_mul_le).trans (by omega)
  · exact (Polynomial.natDegree_mul_le).trans (by omega)

theorem series_eq_of_mul_eq_trunc {F : Type*} [Field F] (M : ℕ) (G : F[X]) (hG : G.coeff 0 = 1)
    (u : PowerSeries F) (A : F[X])
    (h : ∀ j < M, PowerSeries.coeff j (u * (G : PowerSeries F)) =
      PowerSeries.coeff j ((A * G : F[X]) : PowerSeries F)) :
    ∀ j < M, PowerSeries.coeff j u = A.coeff j := by
  have hG0 : PowerSeries.constantCoeff (G : PowerSeries F) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hG]; exact one_ne_zero
  have hW : ∀ j < M, PowerSeries.coeff j ((u - (A : PowerSeries F)) * (G : PowerSeries F)) = 0 := by
    intro j hj
    rw [sub_mul, map_sub, h j hj, Polynomial.coe_mul, sub_self]
  intro j hj
  have e : u - (A : PowerSeries F) = (u - (A : PowerSeries F)) * (G : PowerSeries F) *
      (G : PowerSeries F)⁻¹ := by
    rw [mul_assoc, PowerSeries.mul_inv_cancel _ hG0, mul_one]
  have : PowerSeries.coeff j (u - (A : PowerSeries F)) = 0 := by
    rw [e, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hW x.1 (by omega), zero_mul]
  rw [map_sub, Polynomial.coeff_coe] at this
  exact sub_eq_zero.1 this

theorem coprime_contra (M p : ℕ) (hM : 3 ≤ M) (G C : CohField[X]) (hcop : IsCoprime G C)
    (hG0 : G.coeff 0 = 1) (hGdeg : 0 < G.natDegree) (hGle : G.natDegree ≤ M - 1)
    (hCle : C.natDegree ≤ M - 1)
    (hT : clippedOp M G C (PowerSeries.X * letterSeries ^ p) = 0) (hp : 1 ≤ p) : False := by
  have h1 : G * PowerSeries.trunc M (PowerSeries.X * letterSeries ^ p * (C : PowerSeries CohField))
      = C * PowerSeries.trunc M (PowerSeries.X * letterSeries ^ p * (G : PowerSeries CohField)) :=
    sub_eq_zero.1 hT
  have hdvd : G ∣ PowerSeries.trunc M (PowerSeries.X * letterSeries ^ p *
      (G : PowerSeries CohField)) :=
    hcop.dvd_of_dvd_mul_left ⟨_, h1.symm⟩
  obtain ⟨A, hA⟩ := hdvd
  have hcongr : ∀ j < M, PowerSeries.coeff j (PowerSeries.X * letterSeries ^ p *
      (G : PowerSeries CohField)) = PowerSeries.coeff j ((A * G : CohField[X]) :
        PowerSeries CohField) := by
    intro j hj
    rw [mul_comm A G, ← hA, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hj]
  have hcoeff := series_eq_of_mul_eq_trunc M G hG0 _ A hcongr (M - 1) (by omega)
  have hA0 : A.coeff (M - 1) = 0 := by
    by_cases hA' : A = 0
    · rw [hA']; simp
    · have hdeg : (G * A).natDegree ≤ M - 1 := by
        rw [← hA]
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [PowerSeries.coeff_trunc, if_neg (by omega)]
      have hGne : G ≠ 0 := fun h => by simp [h] at hGdeg
      rw [Polynomial.natDegree_mul hGne hA'] at hdeg
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hA0, show M - 1 = (M - 2) + 1 by omega, PowerSeries.coeff_succ_X_mul] at hcoeff
  have hQ : (1 : PowerSeries CohField) ∈ seriesOverRange (lowerField (M - 2)) := by
    rw [mem_seriesOverRange_iff]; intro i
    rw [PowerSeries.coeff_one]; split_ifs
    exacts [(lowerField _).one_mem, (lowerField _).zero_mem]
  obtain ⟨w, hw, hdec⟩ := coeff_pow_mul_decomp (M - 2) (by omega) p 1 hQ
  rw [mul_one, map_one, mul_one] at hdec
  have hθF : cohLetters 0 ∈ lowerField (M - 2) := letter_mem_lowerField (by omega)
  have hu : (p : CohField) * cohLetters 0 ^ (p - 1) ∈ lowerField (M - 2) :=
    (lowerField _).mul_mem ((lowerField _).natCast_mem p) (pow_mem hθF _)
  have e : (p * cohLetters 0 ^ (p - 1)) * cohLetters (M - 2) + w = 0 := by
    rw [hcoeff] at hdec; linear_combination -hdec
  obtain ⟨h3, -⟩ := eq_zero_of_mul_add_eq_zero (F := (lowerField (M - 2)).toSubfield)
    (letter_notMem_lowerField (M - 2)) hu hw e
  exact mul_ne_zero (natCast_ne_zero_field p hp) (pow_ne_zero _ cohLetters_zero_ne_zero) h3

theorem dS_X (m : ℕ) : dS m (PowerSeries.X : PowerSeries CohField) = 0 := by
  ext i
  rw [coeff_dS, map_zero, PowerSeries.coeff_X]
  split_ifs
  · exact dRaw_one m
  · exact dRaw_zero m

theorem clippedOp_X_pow_pred (M : ℕ) (hM : 1 ≤ M) (G C : CohField[X]) (hC : C.coeff 0 = 1)
    (hG : G.coeff 0 = 1) :
    clippedOp M G C (PowerSeries.X ^ (M - 1)) = (G - C) * Polynomial.X ^ (M - 1) := by
  unfold clippedOp
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [trunc_succ_X_pow_mul, trunc_succ_X_pow_mul, Polynomial.coeff_coe, Polynomial.coeff_coe, hC,
    hG]
  simp only [map_one, one_mul]
  ring

theorem dS_xhp (m p : ℕ) :
    dS m (PowerSeries.X * letterSeries ^ p) =
      PowerSeries.X ^ (m + 1) * (PowerSeries.C (p : CohField) * letterSeries ^ (p - 1)) := by
  rw [dS_mul, dS_X, dS_pow', show dS m letterSeries = _ from dS_mk_letters m]
  ring

theorem potential_divDeriv (m : ℕ) (P Q : ℚ[X]) (hQ : Q ≠ 0) : DivDeriv m (potential P Q) := by
  unfold potential
  refine (divDeriv_aeval m P).mul (divDeriv_inv m _ (divDeriv_aeval m Q) ?_)
  rw [constantCoeff_aeval_letterSeries]; exact aeval_theta_ne_zero hQ

theorem potential_const_ne (Q : ℚ[X]) (hQ : Q ≠ 0) :
    PowerSeries.constantCoeff (Polynomial.aeval letterSeries Q) ≠ 0 := by
  rw [constantCoeff_aeval_letterSeries]; exact aeval_theta_ne_zero hQ

theorem neither_absurd_poly (M : ℕ) (hM : 3 ≤ M) (G C : CohField[X]) (hG0 : G.coeff 0 = 1)
    (hC0 : C.coeff 0 = 1) (hGle : G.natDegree ≤ M - 1) (hCle : C.natDegree ≤ M - 1)
    (hGdeg : 0 < G.natDegree) (hcop : IsCoprime G C) (hne : G ≠ C)
    (dG : dS (M - 1) (G : PowerSeries CohField) = 0) (dC : dS (M - 1) (C : PowerSeries CohField) = 0)
    (hdef : ∀ k ≤ M, (clippedOp M G C letterSeries).coeff k = 0) {p : ℕ} (hp : 1 ≤ p)
    (P Q : ℚ[X]) (hQ : Q ≠ 0)
    (heq : ∀ k < 2 * M, PowerSeries.coeff k
      (((clippedOp M G C (PowerSeries.X * letterSeries ^ p) : CohField[X]) :
          PowerSeries CohField) + PowerSeries.X *
        ((clippedOp M G C letterSeries : CohField[X]) : PowerSeries CohField) *
          potential P Q) = 0) : False := by
  obtain ⟨ψ, hψ⟩ := potential_divDeriv (M - 1) P Q hQ
  set r := potential P Q with hr
  set Dfct := clippedOp M G C letterSeries with hDfct
  have hMm : M - 1 + 1 = M := by omega
  -- the derivative of the power equation
  have hz : ∀ k < 2 * M, PowerSeries.coeff k (dS (M - 1)
      (((clippedOp M G C (PowerSeries.X * letterSeries ^ p) : CohField[X]) :
          PowerSeries CohField) + PowerSeries.X * (Dfct : PowerSeries CohField) * r)) = 0 := by
    intro k hk
    rw [coeff_dS, heq k hk, dRaw_zero]
  have hT1 : clippedOp M G C (dS (M - 1) (PowerSeries.X * letterSeries ^ p)) = 0 := by
    rw [dS_xhp, hMm]
    unfold clippedOp
    have e1 : ∀ (X' : PowerSeries CohField), PowerSeries.X ^ M * (PowerSeries.C (p : CohField) *
        letterSeries ^ (p - 1)) * X' = PowerSeries.X ^ M * (PowerSeries.C (p : CohField) *
        letterSeries ^ (p - 1) * X') := fun X' => by ring
    rw [e1, e1, trunc_X_pow_mul_self, trunc_X_pow_mul_self]; simp
  have hdS : dS (M - 1)
      (((clippedOp M G C (PowerSeries.X * letterSeries ^ p) : CohField[X]) :
          PowerSeries CohField) + PowerSeries.X * (Dfct : PowerSeries CohField) * r) =
      PowerSeries.X * (((G - C) * Polynomial.X ^ (M - 1) : CohField[X]) : PowerSeries CohField) * r +
        PowerSeries.X * (Dfct : PowerSeries CohField) * (PowerSeries.X ^ (M - 1) * ψ) := by
    rw [dS_add, dS_clippedOp (M - 1) M G C _ dG dC, hT1, dS_mul, dS_mul, dS_X, zero_mul, zero_add, hψ,
      hDfct, dS_clippedOp (M - 1) M G C _ dG dC, show dS (M - 1) letterSeries = _ from dS_mk_letters _,
      clippedOp_X_pow_pred M (by omega) G C hC0 hG0]
    simp
  have hdne : G - C ≠ 0 := sub_ne_zero.2 hne
  set d := (G - C).natTrailingDegree with hd
  have hdle : d ≤ (G - C).natDegree := Polynomial.natTrailingDegree_le_natDegree _
  have hdeg : (G - C).natDegree ≤ M - 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hGle hCle)
  have hk := hz (M + d) (by omega)
  rw [hdS] at hk
  have e1 : PowerSeries.X * (((G - C) * Polynomial.X ^ (M - 1) : CohField[X]) :
      PowerSeries CohField) * r = PowerSeries.X ^ M * (((G - C : CohField[X]) :
        PowerSeries CohField) * r) := by
    rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
    conv_rhs => rw [← hMm, pow_succ]
    ring
  have e2 : PowerSeries.X * (Dfct : PowerSeries CohField) * (PowerSeries.X ^ (M - 1) * ψ) =
      PowerSeries.X ^ M * ((Dfct : PowerSeries CohField) * ψ) := by
    conv_rhs => rw [← hMm, pow_succ]
    ring
  rw [e1, e2, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    if_pos (by omega), Nat.add_sub_cancel_left,
    coeff_defect_mul_eq_zero Dfct ψ M d hdef (by omega), add_zero] at hk
  have hsum : PowerSeries.coeff d (((G - C : CohField[X]) : PowerSeries CohField) * r) =
      (G - C).coeff d * PowerSeries.constantCoeff r := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (d, 0)]
    · rw [Polynomial.coeff_coe, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    · rintro ⟨i, j⟩ hij hne'
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      have hid : i ≠ d := fun h => hne' (by simp only [Prod.mk.injEq]; omega)
      rw [Polynomial.coeff_coe]
      rcases lt_or_gt_of_ne hid with h | h
      · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree h, zero_mul]
      · omega
    · intro h; exact absurd (by simp) h
  rw [hsum] at hk
  have hlead : (G - C).coeff d ≠ 0 := by
    have := mt Polynomial.trailingCoeff_eq_zero.1 hdne
    exact this
  have hr0 : PowerSeries.constantCoeff r = 0 := by
    rcases mul_eq_zero.1 hk with h | h
    · exact absurd h hlead
    · exact h
  have hP : Polynomial.aeval letterSeries P = 0 := by
    have : PowerSeries.constantCoeff (Polynomial.aeval letterSeries P) = 0 := by
      have h' : PowerSeries.constantCoeff r =
          PowerSeries.constantCoeff (Polynomial.aeval letterSeries P) *
            (PowerSeries.constantCoeff (Polynomial.aeval letterSeries Q))⁻¹ := by
        rw [hr]; unfold potential
        rw [map_mul, PowerSeries.constantCoeff_inv]
      rw [h'] at hr0
      rcases mul_eq_zero.1 hr0 with h | h
      · exact h
      · exact absurd (inv_eq_zero.1 h) (potential_const_ne Q hQ)
    rw [constantCoeff_aeval_letterSeries] at this
    have hP0 := aeval_theta_eq_zero this
    rw [hP0, map_zero]
  have hr_zero : r = 0 := by rw [hr]; unfold potential; rw [hP, zero_mul]
  have hTzero : clippedOp M G C (PowerSeries.X * letterSeries ^ p) = 0 := by
    have hdegT := natDegree_clippedOp_le M G C (PowerSeries.X * letterSeries ^ p) hGle hCle
      (by omega)
    ext j
    rw [Polynomial.coeff_zero]
    by_cases hj : j < 2 * M
    · have := heq j hj
      rw [hr_zero, mul_zero, add_zero] at this
      rwa [Polynomial.coeff_coe] at this
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  exact coprime_contra M p hM G C hcop hG0 hGdeg hGle hCle hTzero hp

end SkewCoframeRigidity.Coframe
