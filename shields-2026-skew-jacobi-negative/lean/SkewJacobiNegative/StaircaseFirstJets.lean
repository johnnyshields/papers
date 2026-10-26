/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseResidualAlgebra

/-!
# Actual staircase first coefficients

Restriction and first-coefficient operators for `thm:staircase-first-jet` in
`shields-2026-skew-jacobi-negative.tex`.  The univariate marking keeps the
actual independent generator, not a surrogate determinant.  In particular,
equalities here concern full Schur functions, not profile equality.
-/

namespace SkewJacobiNegative.Staircase

open Gluing HessenbergExpansion
attribute [local simp] Polynomial.coeff_X Polynomial.coeff_one

/-- The coefficient of the first power of the cut generator. -/
noncomputable def firstCoefficient (q : ℕ+) (p : CompleteRing) : CompleteRing :=
  eraseGenerator q (MvPolynomial.pderiv q p)

@[simp] theorem minimumPolynomial_X (q v : ℕ+) :
    minimumPolynomial q (MvPolynomial.X v : CompleteRing) =
      if v = q then Polynomial.X else Polynomial.C (MvPolynomial.X v) := by
  simp [minimumPolynomial]

/-- Every marking has an exact left inverse at the actual complete generator. -/
theorem minimumPolynomial_eval (q : ℕ+) (p : CompleteRing) :
    (minimumPolynomial q p).eval (MvPolynomial.X q) = p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [minimumPolynomial]
  | add p r hp hr => simp [map_add, hp, hr]
  | mul_X p v hp =>
    rw [map_mul, minimumPolynomial_X]
    by_cases hv : v = q
    · subst v
      simp [hp]
    · simp [hv, hp]

/-- Keeping all univariate coefficients loses no full-function information. -/
theorem minimumPolynomial_injective (q : ℕ+) : Function.Injective (minimumPolynomial q) := by
  intro p r he
  have h := congrArg (fun f : Polynomial CompleteRing => f.eval (MvPolynomial.X q)) he
  simpa only [minimumPolynomial_eval] using h

/-- The constant marked coefficient is exactly generator erasure. -/
theorem minimumPolynomial_coeff_zero (q : ℕ+) (p : CompleteRing) :
    (minimumPolynomial q p).coeff 0 = eraseGenerator q p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [minimumPolynomial, eraseGenerator]
  | add p r hp hr => simp [map_add, hp, hr]
  | mul_X p v hp =>
    rw [map_mul, minimumPolynomial_X]
    by_cases hv : v = q
    · subst v
      simp [eraseGenerator, hp]
    · simp [eraseGenerator, hv, hp]

/-- The first marked coefficient is the actual first power, not the raw derivative. -/
theorem minimumPolynomial_coeff_one (q : ℕ+) (p : CompleteRing) :
    (minimumPolynomial q p).coeff 1 = firstCoefficient q p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [minimumPolynomial, firstCoefficient, MvPolynomial.pderiv_C]
  | add p r hp hr => simp [map_add, firstCoefficient] at hp hr ⊢; rw [hp, hr]
  | mul_X p v hp =>
    rw [map_mul, minimumPolynomial_X]
    by_cases hv : v = q
    · subst v
      simp [firstCoefficient, MvPolynomial.pderiv_mul, eraseGenerator,
        minimumPolynomial_coeff_zero]
    · simp [firstCoefficient, MvPolynomial.pderiv_mul, eraseGenerator, hv, hp, mul_comm]

/-- First jets recover every genuinely affine polynomial in the cut generator. -/
theorem eq_of_first_jet_of_degree_le_one (q : ℕ+) (p r : CompleteRing)
    (hp : (minimumPolynomial q p).natDegree ≤ 1)
    (hr : (minimumPolynomial q r).natDegree ≤ 1)
    (hzero : eraseGenerator q p = eraseGenerator q r)
    (hone : firstCoefficient q p = firstCoefficient q r) : p = r := by
  apply minimumPolynomial_injective q
  apply Polynomial.ext
  intro k
  rcases k with _ | k
  · simpa only [minimumPolynomial_coeff_zero] using hzero
  rcases k with _ | k
  · change (minimumPolynomial q p).coeff 1 = (minimumPolynomial q r).coeff 1
    simpa only [minimumPolynomial_coeff_one] using hone
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- A noncontact complete generator is a constant in the marked polynomial. -/
theorem minimumPolynomial_complete_ne (q : ℕ+) (k : ℤ) (hk : k ≠ (q.val : ℤ)) :
    minimumPolynomial q (complete k) = Polynomial.C (complete k) := by
  rw [minimumPolynomial_complete, if_neg hk]

private theorem map_marked_atom (A : Prop) [Decidable A]
    (c : CompleteRing) (hc : residualAugmentation c = 1) :
    ((if A then Polynomial.X else Polynomial.C c) : Polynomial CompleteRing).map
        residualAugmentation = if A then Polynomial.X else 1 := by
  by_cases hA : A <;> simp [hA,hc]

private theorem marked_generator_affine (q : ℕ+) (k : ℤ) :
    (if k = (q.val : ℤ) then Polynomial.X else Polynomial.C (complete k)) =
      Polynomial.C (bar q k)+Polynomial.X*Polynomial.C
        (if k = (q.val : ℤ) then (1 : CompleteRing) else 0) := by
  by_cases hk : k = (q.val : ℤ) <;>
    simp [hk,bar,eraseGenerator_complete]

private theorem indicator_pair (A B : Prop) [Decidable A] [Decidable B] (c : CompleteRing) :
    (if A then (1 : CompleteRing) else 0)*(if B then 1 else 0)*c =
      if A ∧ B then c else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA,hB]

private theorem indicator_triple (A B C : Prop)
    [Decidable A] [Decidable B] [Decidable C] (d : CompleteRing) :
    (if A then (1 : CompleteRing) else 0)*(if B then 1 else 0)*
      (if C then 1 else 0)*d = if A ∧ B ∧ C then d else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA,hB,hC]

private theorem three_affine_coeff_two (a b u α β υ c r v s t : CompleteRing) :
    (((Polynomial.C a+Polynomial.X*Polynomial.C α)*
        (Polynomial.C b+Polynomial.X*Polynomial.C β)*Polynomial.C c-
      (Polynomial.C u+Polynomial.X*Polynomial.C υ)*Polynomial.C r*Polynomial.C c-
      (Polynomial.C a+Polynomial.X*Polynomial.C α)*Polynomial.C v*Polynomial.C s+
      Polynomial.C t*Polynomial.C r*Polynomial.C s).coeff 2) = α*β*c := by
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ] <;> ring

private theorem four_affine_coeff_two
    (a b c u v x α β γ υ ν ξ r s t d W Y T : CompleteRing) :
    (((Polynomial.C a+Polynomial.X*Polynomial.C α)*
          (Polynomial.C b+Polynomial.X*Polynomial.C β)*
          (Polynomial.C c+Polynomial.X*Polynomial.C γ)*Polynomial.C d-
      (Polynomial.C u+Polynomial.X*Polynomial.C υ)*Polynomial.C r*
          (Polynomial.C c+Polynomial.X*Polynomial.C γ)*Polynomial.C d-
      (Polynomial.C a+Polynomial.X*Polynomial.C α)*
          (Polynomial.C v+Polynomial.X*Polynomial.C ν)*Polynomial.C s*Polynomial.C d-
      (Polynomial.C a+Polynomial.X*Polynomial.C α)*
          (Polynomial.C b+Polynomial.X*Polynomial.C β)*Polynomial.C W*Polynomial.C t+
      (Polynomial.C x+Polynomial.X*Polynomial.C ξ)*Polynomial.C r*Polynomial.C s*Polynomial.C d+
      (Polynomial.C u+Polynomial.X*Polynomial.C υ)*Polynomial.C r*Polynomial.C W*Polynomial.C t+
      (Polynomial.C a+Polynomial.X*Polynomial.C α)*Polynomial.C Y*Polynomial.C s*Polynomial.C t-
      Polynomial.C T*Polynomial.C r*Polynomial.C s*Polynomial.C t).coeff 2) =
      (α*β)*(c*d-t*W)+(α*γ)*(b*d)+(β*γ)*(a*d)-
        (υ*γ)*(r*d)-(α*ν)*(s*d) := by
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ] <;> ring

private theorem four_affine_coeff_three
    (a b c u v x α β γ υ ν ξ r s t d W Y T : CompleteRing) :
    (((Polynomial.C a+Polynomial.X*Polynomial.C α)*
          (Polynomial.C b+Polynomial.X*Polynomial.C β)*
          (Polynomial.C c+Polynomial.X*Polynomial.C γ)*Polynomial.C d-
      (Polynomial.C u+Polynomial.X*Polynomial.C υ)*Polynomial.C r*
          (Polynomial.C c+Polynomial.X*Polynomial.C γ)*Polynomial.C d-
      (Polynomial.C a+Polynomial.X*Polynomial.C α)*
          (Polynomial.C v+Polynomial.X*Polynomial.C ν)*Polynomial.C s*Polynomial.C d-
      (Polynomial.C a+Polynomial.X*Polynomial.C α)*
          (Polynomial.C b+Polynomial.X*Polynomial.C β)*Polynomial.C W*Polynomial.C t+
      (Polynomial.C x+Polynomial.X*Polynomial.C ξ)*Polynomial.C r*Polynomial.C s*Polynomial.C d+
      (Polynomial.C u+Polynomial.X*Polynomial.C υ)*Polynomial.C r*Polynomial.C W*Polynomial.C t+
      (Polynomial.C a+Polynomial.X*Polynomial.C α)*Polynomial.C Y*Polynomial.C s*Polynomial.C t-
      Polynomial.C T*Polynomial.C r*Polynomial.C s*Polynomial.C t).coeff 3) = α*β*γ*d := by
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ] <;> ring

/-- The entire four-row marked polynomial, before choosing a contact stratum. -/
theorem four_marked_expansion {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    minimumPolynomial q P.toBetaDiagram.schur =
      fourInterval (fun k => if k = (q.val : ℤ) then Polynomial.X else
        Polynomial.C (complete k))
        (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2) := by
  rw [Profile.toBetaDiagram_schur, Profile.schur_four_interval P hP.thick.hessenberg]
  simp only [fourInterval, ← complete_eq_hh, map_sub, map_add, map_mul,
    minimumPolynomial_complete]

/-- The entire three-row marking likewise comes from the actual determinant. -/
theorem three_marked_expansion {q : ℕ+} {P : Profile 2} (hP : QComponent q P) :
    minimumPolynomial q P.toBetaDiagram.schur =
      threeInterval (fun k => if k = (q.val : ℤ) then Polynomial.X else
        Polynomial.C (complete k))
        (P.r 0) (P.r 1) (P.r 2) (P.g 0) (P.g 1) := by
  rw [three_full_interval hP]
  simp only [threeInterval, map_add, map_sub, map_mul, minimumPolynomial_complete]

/-- Through two rows the inherited boundary leaves only the first-row contact. -/
theorem two_full_affine {q : ℕ+} {P : Profile 1} (hP : QComponent q P) :
    minimumPolynomial q P.toBetaDiagram.schur =
      (if P.r 0 = q.val then Polynomial.X else Polynomial.C (complete (P.r 0))) *
        Polynomial.C (complete (P.r 1)) -
      Polynomial.C (complete ((P.r 0 : ℤ) + P.r 1 - P.g 0) * complete (P.g 0)) := by
  have hb : q.val + P.g 0 < P.r 1 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hg : (P.g 0 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 0
  have hu : (q.val : ℤ) < (P.r 0 : ℤ) + P.r 1 - P.g 0 := by
    have := P.r_pos 0
    omega
  unfold BetaDiagram.schur
  rw [Matrix.det_fin_two]
  have h0 := P.xi_sub_zeta (0 : Fin 2)
  have h1 := P.xi_sub_zeta (1 : Fin 2)
  have hgap := P.xi_succ_sub_zeta_castSucc (0 : Fin 1)
  change P.xi 1 - P.zeta 0 = (P.g 0 : ℤ) at hgap
  have hfull : P.xi 0 - P.zeta 1 = (P.r 0 : ℤ) + P.r 1 - P.g 0 := by omega
  simp only [BetaDiagram.matrix, Profile.toBetaDiagram, Matrix.of_apply,
    h0, h1, hgap, hfull, map_sub, map_mul, minimumPolynomial_complete,
    if_neg (show (P.r 1 : ℤ) ≠ q.val by omega), if_neg hg,
    if_neg (ne_of_gt hu)]
  have hA : (P.r 0 : ℤ) = q.val ↔ P.r 0 = q.val := by omega
  simp only [hA]

/-- No extra polynomial-degree assumption is carried in the two-row result. -/
theorem two_marked_degree_le_one {q : ℕ+} {P : Profile 1} (hP : QComponent q P) :
    (minimumPolynomial q P.toBetaDiagram.schur).natDegree ≤ 1 := by
  rw [two_full_affine hP]
  split_ifs
  · apply (Polynomial.natDegree_sub_le _ _).trans
    refine max_le ?_ ?_
    · exact (Polynomial.natDegree_mul_C_le _ _).trans (by simp)
    · simp only [← Polynomial.C_mul,Polynomial.natDegree_C]
      omega
  · simp only [← Polynomial.C_mul, ← Polynomial.C_sub, Polynomial.natDegree_C]
    omega

/-- Faithful first-jet rigidity for actual two-row components, with arbitrary contacts. -/
theorem staircase_first_jet_two {q : ℕ+} {P Q : Profile 1}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur :=
  eq_of_first_jet_of_degree_le_one q _ _ (two_marked_degree_le_one hP)
    (two_marked_degree_le_one hQ) hzero hone

/-- Singleton components are independent of q by their inherited boundary. -/
theorem singleton_marked_constant {q : ℕ+} {P : Profile 0} (hP : QComponent q P) :
    minimumPolynomial q P.toBetaDiagram.schur = Polynomial.C (complete (P.r 0)) := by
  have hb : q.val < P.r 0 := by simpa [lastGap] using hP.bottom
  have he : P.toBetaDiagram.schur = complete (P.r 0) := by
    rw [BetaDiagram.schur, Matrix.det_fin_one]
    change complete (P.xi 0 - P.zeta 0) = complete (P.r 0)
    rw [P.xi_sub_zeta]
  rw [he, minimumPolynomial_complete_ne q _ (by omega)]

/-- Faithful singleton first-jet rigidity, without a profile-equality assertion. -/
theorem staircase_first_jet_singleton {q : ℕ+} {P Q : Profile 0}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hzero : restriction q P = restriction q Q) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  apply minimumPolynomial_injective q
  rw [singleton_marked_constant hP, singleton_marked_constant hQ]
  have hh := congrArg (fun p : CompleteRing => p) hzero
  have hzP := minimumPolynomial_coeff_zero q P.toBetaDiagram.schur
  have hzQ := minimumPolynomial_coeff_zero q Q.toBetaDiagram.schur
  rw [singleton_marked_constant hP, Polynomial.coeff_C_zero] at hzP
  rw [singleton_marked_constant hQ, Polynomial.coeff_C_zero] at hzQ
  change eraseGenerator q P.toBetaDiagram.schur = eraseGenerator q Q.toBetaDiagram.schur at hh
  rw [← hzP, ← hzQ] at hh
  exact congrArg Polynomial.C hh

/-- The boundary leaves only a, b, and their merged interval as three-row contacts. -/
theorem three_marked_core {q : ℕ+} {P : Profile 2} (hP : QComponent q P) :
    minimumPolynomial q P.toBetaDiagram.schur =
      (if (P.r 0 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 0))) *
        (if (P.r 1 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 1))) *
        Polynomial.C (complete (P.r 2)) -
      (if (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val then Polynomial.X else
        Polynomial.C (complete ((P.r 0 : ℤ) + P.r 1 - P.g 0))) *
        Polynomial.C (complete (P.g 0)) * Polynomial.C (complete (P.r 2)) -
      (if (P.r 0 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 0))) *
        Polynomial.C (complete ((P.r 1 : ℤ) + P.r 2 - P.g 1)) *
        Polynomial.C (complete (P.g 1)) +
      Polynomial.C (complete ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1)) *
        Polynomial.C (complete (P.g 0)) * Polynomial.C (complete (P.g 1)) := by
  have hb : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hsb : P.g 1 < P.r 1 := P.g_lt_castSucc 1
  have hra : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hrq : (P.g 0 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 0
  have hsq : (P.g 1 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 1
  rw [three_marked_expansion hP]
  simp only [threeInterval, if_neg (show (P.r 2 : ℤ) ≠ q.val by omega),
    if_neg hrq, if_neg hsq,
    if_neg (show (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val by omega),
    if_neg (show (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 ≠ q.val by omega)]

private theorem three_core_degree (A B U : Polynomial CompleteRing)
    (c r v s t : CompleteRing) (hA : A.natDegree ≤ 1)
    (hB : B.natDegree ≤ 1) (hU : U.natDegree ≤ 1) :
    (A * B * Polynomial.C c - U * Polynomial.C r * Polynomial.C c -
      A * Polynomial.C v * Polynomial.C s +
      Polynomial.C t * Polynomial.C r * Polynomial.C s).natDegree ≤ 2 := by
  have h1 : (A * B * Polynomial.C c).natDegree ≤ 2 :=
    (Polynomial.natDegree_mul_C_le _ _).trans
      (Polynomial.natDegree_mul_le.trans (by omega))
  have h2 : (U * Polynomial.C r * Polynomial.C c).natDegree ≤ 2 :=
    (Polynomial.natDegree_mul_C_le _ _).trans
      ((Polynomial.natDegree_mul_C_le _ _).trans (by omega))
  have h3 : (A * Polynomial.C v * Polynomial.C s).natDegree ≤ 2 :=
    (Polynomial.natDegree_mul_C_le _ _).trans
      ((Polynomial.natDegree_mul_C_le _ _).trans (by omega))
  have h4 : (Polynomial.C t * Polynomial.C r * Polynomial.C s).natDegree ≤ 2 := by
    simp only [← Polynomial.C_mul, Polynomial.natDegree_C]
    omega
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le ((Polynomial.natDegree_sub_le _ _).trans
      (max_le ((Polynomial.natDegree_sub_le _ _).trans (max_le h1 h2)) h3)) h4)

/-- The three-row marking has no unrecorded third or higher coefficient. -/
theorem three_marked_degree_le_two {q : ℕ+} {P : Profile 2} (hP : QComponent q P) :
    (minimumPolynomial q P.toBetaDiagram.schur).natDegree ≤ 2 := by
  rw [three_marked_core hP]
  apply three_core_degree
  all_goals split_ifs <;> simp

/-- Its only quadratic term is the double first-row contact. -/
theorem three_marked_coeff_two {q : ℕ+} {P : Profile 2} (hP : QComponent q P) :
    (minimumPolynomial q P.toBetaDiagram.schur).coeff 2 =
      if P.r 0 = q.val ∧ P.r 1 = q.val then complete (P.r 2) else 0 := by
  classical
  rw [three_marked_core hP]
  simp_rw [marked_generator_affine]
  rw [three_affine_coeff_two]
  have hA : (P.r 0 : ℤ) = q.val ↔ P.r 0 = q.val := by omega
  have hB : (P.r 1 : ℤ) = q.val ↔ P.r 1 = q.val := by omega
  simp only [hA,hB,indicator_pair]

private theorem scalar_three_double_iff (q a b u : ℤ) (hua : a < u) (hub : b < u) :
    let f : Polynomial ℚ :=
      (if a = q then Polynomial.X else 1)*(if b = q then Polynomial.X else 1)-
        (if u = q then Polynomial.X else 1)-(if a = q then Polynomial.X else 1)+1
    (f.coeff 0 = 0 ∧ f.coeff 1 = -1) ↔ a = q ∧ b = q := by
  dsimp only
  by_cases ha : a = q <;> by_cases hb : b = q <;> by_cases hu : u = q
  all_goals simp [ha,hb,hu,Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ] <;> omega

/-- The scalar first jet identifies the double-row contact, without any residual
classification theorem or distinct-index assumption. -/
theorem three_double_contact_iff {q : ℕ+} {P : Profile 2} (hP : QComponent q P) :
    (residualAugmentation (restriction q P) = 0 ∧
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) = -1) ↔
        P.r 0 = q.val ∧ P.r 1 = q.val := by
  classical
  have hra : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hrb : P.g 0 < P.r 1 := P.g_lt_succ 0
  have hsb : P.g 1 < P.r 1 := P.g_lt_castSucc 1
  have hc : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hrow0 := residualAugmentation_complete (show (0 : ℤ) < P.r 0 by
    exact_mod_cast P.r_pos 0)
  have hrow1 := residualAugmentation_complete (show (0 : ℤ) < P.r 1 by
    exact_mod_cast P.r_pos 1)
  have hrow2 := residualAugmentation_complete (show (0 : ℤ) < P.r 2 by
    exact_mod_cast P.r_pos 2)
  have hgap0 := residualAugmentation_complete (show (0 : ℤ) < P.g 0 by
    exact_mod_cast hP.gap_pos 0)
  have hgap1 := residualAugmentation_complete (show (0 : ℤ) < P.g 1 by
    exact_mod_cast hP.gap_pos 1)
  have hU := residualAugmentation_complete
    (show 0 < (P.r 0 : ℤ) + P.r 1 - P.g 0 by omega)
  have hV := residualAugmentation_complete
    (show 0 < (P.r 1 : ℤ) + P.r 2 - P.g 1 by omega)
  have hT := residualAugmentation_complete
    (show 0 < (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 by omega)
  have hmap : (minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation =
      (if (P.r 0 : ℤ) = q.val then Polynomial.X else 1)*
        (if (P.r 1 : ℤ) = q.val then Polynomial.X else 1)-
      (if (P.r 0 : ℤ)+P.r 1-P.g 0 = q.val then Polynomial.X else 1)-
      (if (P.r 0 : ℤ) = q.val then Polynomial.X else 1)+1 := by
    rw [three_marked_core hP]
    simp only [Polynomial.map_add,Polynomial.map_sub,Polynomial.map_mul,
      map_marked_atom _ _ hrow0,map_marked_atom _ _ hrow1,map_marked_atom _ _ hU,
      Polynomial.map_C,hrow2,hgap0,hgap1,hV,hT,Polynomial.C_1,one_mul,mul_one]
  have hz : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 0 =
      residualAugmentation (restriction q P) := by
    simp only [Polynomial.coeff_map,minimumPolynomial_coeff_zero,restriction]
  have ho : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 1 =
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) := by
    simp only [Polynomial.coeff_map,minimumPolynomial_coeff_one]
  rw [← hz,← ho,hmap]
  have hA : (P.r 0 : ℤ) = q.val ↔ P.r 0 = q.val := by omega
  have hB : (P.r 1 : ℤ) = q.val ↔ P.r 1 = q.val := by omega
  simpa only [hA,hB] using scalar_three_double_iff q.val (P.r 0) (P.r 1)
    ((P.r 0 : ℤ)+P.r 1-P.g 0) (by omega) (by omega)

/-- Exact first coefficient on that contact, including repeated gap labels. -/
theorem three_double_first_coefficient {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      -complete (P.g 1) * complete ((q.val : ℤ) + P.r 2 - P.g 1) := by
  rw [← minimumPolynomial_coeff_one, three_marked_core hP]
  have hr0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hrq : P.g 0 < q.val := by omega
  have hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by
    have := q.pos
    omega
  have ha' : (P.r 0 : ℤ) = q.val := by exact_mod_cast ha
  have hb' : (P.r 1 : ℤ) = q.val := by exact_mod_cast hb
  simp only [if_pos ha', if_pos hb', if_neg hu]
  norm_num [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp (failIfUnchanged := false) only [hb] <;> ring

/-- Full-function first-jet rigidity through three rows; the double-contact
quadratic coefficient is recovered from the actual scalar and polynomial jets. -/
theorem staircase_first_jet_three {q : ℕ+} {P Q : Profile 2}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hcontact : (P.r 0 = q.val ∧ P.r 1 = q.val) ↔
      Q.r 0 = q.val ∧ Q.r 1 = q.val := by
    rw [← three_double_contact_iff hP, ← three_double_contact_iff hQ, hzero, hone]
  have htwo : (minimumPolynomial q P.toBetaDiagram.schur).coeff 2 =
      (minimumPolynomial q Q.toBetaDiagram.schur).coeff 2 := by
    rw [three_marked_coeff_two hP, three_marked_coeff_two hQ]
    by_cases hp : P.r 0 = q.val ∧ P.r 1 = q.val
    · have hq := hcontact.mp hp
      rw [if_pos hp, if_pos hq]
      have he := hone
      rw [three_double_first_coefficient hP hp.1 hp.2,
        three_double_first_coefficient hQ hq.1 hq.2] at he
      have hpairs : complete (P.g 1) * complete ((q.val : ℤ) + P.r 2 - P.g 1) =
          complete (Q.g 1) * complete ((q.val : ℤ) + Q.r 2 - Q.g 1) := by
        linear_combination -he
      have hpg : P.g 1 < P.r 1 := P.g_lt_castSucc 1
      have hqg : Q.g 1 < Q.r 1 := Q.g_lt_castSucc 1
      have hpb := hp.2
      have hqb := hq.2
      have hps : P.g 1 < q.val := by omega
      have hqs : Q.g 1 < q.val := by omega
      have hpc : q.val + P.g 1 < P.r 2 := by
        simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
      have hqc : q.val + Q.g 1 < Q.r 2 := by
        simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
      have hpair := complete_two_product_reading
        (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1)
        (show 0 < (q.val : ℤ) + P.r 2 - P.g 1 by omega)
        (show (0 : ℤ) < Q.g 1 by exact_mod_cast hQ.gap_pos 1)
        (show 0 < (q.val : ℤ) + Q.r 2 - Q.g 1 by omega) hpairs
      rcases hpair with ⟨hs, hc⟩ | ⟨hs, hc⟩
      · have hr : P.r 2 = Q.r 2 := by omega
        rw [hr]
      · omega
    · rw [if_neg hp, if_neg (mt hcontact.mpr hp)]
  apply minimumPolynomial_injective q
  apply Polynomial.ext
  intro k
  rcases k with _ | k
  · simpa only [minimumPolynomial_coeff_zero, restriction] using hzero
  rcases k with _ | k
  · change (minimumPolynomial q P.toBetaDiagram.schur).coeff 1 =
      (minimumPolynomial q Q.toBetaDiagram.schur).coeff 1
    simpa only [minimumPolynomial_coeff_one] using hone
  rcases k with _ | k
  · exact htwo
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (three_marked_degree_le_two hP) (by omega)),
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (three_marked_degree_le_two hQ) (by omega))]

/-- The exact marked eight-term polynomial with all preserved suffix terms constant. -/
theorem four_marked_core {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    minimumPolynomial q P.toBetaDiagram.schur =
      (if (P.r 0 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 0))) *
      (if (P.r 1 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 1))) *
      (if (P.r 2 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 2))) *
        Polynomial.C (complete (P.r 3)) -
      (if (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val then Polynomial.X else
        Polynomial.C (complete ((P.r 0 : ℤ) + P.r 1 - P.g 0))) *
        Polynomial.C (complete (P.g 0)) *
      (if (P.r 2 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 2))) *
        Polynomial.C (complete (P.r 3)) -
      (if (P.r 0 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 0))) *
      (if (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val then Polynomial.X else
        Polynomial.C (complete ((P.r 1 : ℤ) + P.r 2 - P.g 1))) *
        Polynomial.C (complete (P.g 1)) * Polynomial.C (complete (P.r 3)) -
      (if (P.r 0 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 0))) *
      (if (P.r 1 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 1))) *
        Polynomial.C (complete ((P.r 2 : ℤ) + P.r 3 - P.g 2)) *
        Polynomial.C (complete (P.g 2)) +
      (if prefixIndex P = q.val then Polynomial.X else Polynomial.C (complete (prefixIndex P))) *
        Polynomial.C (complete (P.g 0)) * Polynomial.C (complete (P.g 1)) *
        Polynomial.C (complete (P.r 3)) +
      (if (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val then Polynomial.X else
        Polynomial.C (complete ((P.r 0 : ℤ) + P.r 1 - P.g 0))) *
        Polynomial.C (complete (P.g 0)) *
        Polynomial.C (complete ((P.r 2 : ℤ) + P.r 3 - P.g 2)) *
        Polynomial.C (complete (P.g 2)) +
      (if (P.r 0 : ℤ) = q.val then Polynomial.X else Polynomial.C (complete (P.r 0))) *
        Polynomial.C (complete (suffixIndex P)) *
        Polynomial.C (complete (P.g 1)) * Polynomial.C (complete (P.g 2)) -
      Polynomial.C (complete (fullIndex P)) *
        Polynomial.C (complete (P.g 0)) * Polynomial.C (complete (P.g 1)) *
        Polynomial.C (complete (P.g 2)) := by
  have hb : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hct : P.g 2 < P.r 2 := P.g_lt_castSucc 2
  have hbs := hP.thick 1 2 (by decide)
  change P.g 1 + P.g 2 < P.r 2 at hbs
  have hra : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hg0 : (P.g 0 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 0
  have hg1 : (P.g 1 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 1
  have hg2 : (P.g 2 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 2
  rw [four_marked_expansion hP]
  simp only [fourInterval, if_neg hg0, if_neg hg1, if_neg hg2,
    if_neg (show (P.r 3 : ℤ) ≠ q.val by omega),
    if_neg (show (P.r 2 : ℤ) + P.r 3 - P.g 2 ≠ q.val by omega),
    if_neg (show (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 ≠ q.val by omega),
    if_neg (show (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 ≠
      q.val by have := P.r_pos 1; omega), prefixIndex, suffixIndex, fullIndex_four]
  <;> ring

/-- The actual second coefficient, collected before any contact types are named. -/
noncomputable def fourSecondCoefficient (q : ℕ+) (P : Profile 3) : CompleteRing :=
  (if P.r 0 = q.val ∧ P.r 1 = q.val then
    bar q (P.r 2) * complete (P.r 3) -
      complete (P.g 2) * complete ((P.r 2 : ℤ) + P.r 3 - P.g 2) else 0) +
  (if P.r 0 = q.val ∧ P.r 2 = q.val then
    bar q (P.r 1) * complete (P.r 3) else 0) +
  (if P.r 1 = q.val ∧ P.r 2 = q.val then
    bar q (P.r 0) * complete (P.r 3) else 0) -
  (if (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 2 = q.val then
    complete (P.g 0) * complete (P.r 3) else 0) -
  (if P.r 0 = q.val ∧ (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val then
    complete (P.g 1) * complete (P.r 3) else 0)

/-- The only cubic coefficient comes from three contacted diagonal rows. -/
noncomputable def fourThirdCoefficient (q : ℕ+) (P : Profile 3) : CompleteRing :=
  if P.r 0 = q.val ∧ P.r 1 = q.val ∧ P.r 2 = q.val then complete (P.r 3) else 0

set_option maxHeartbeats 0 in
/-- Exact second-coefficient table, valid at every numerical label collision. -/
theorem four_marked_coeff_two {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    (minimumPolynomial q P.toBetaDiagram.schur).coeff 2 = fourSecondCoefficient q P := by
  classical
  rw [four_marked_core hP]
  simp_rw [marked_generator_affine]
  rw [four_affine_coeff_two]
  have hA : (P.r 0 : ℤ) = q.val ↔ P.r 0 = q.val := by omega
  have hB : (P.r 1 : ℤ) = q.val ↔ P.r 1 = q.val := by omega
  have hC : (P.r 2 : ℤ) = q.val ↔ P.r 2 = q.val := by omega
  simp only [hA,hB,hC,indicator_pair,fourSecondCoefficient]

set_option maxHeartbeats 0 in
/-- Exact third-coefficient table, with no distinct-index approximation. -/
theorem four_marked_coeff_three {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    (minimumPolynomial q P.toBetaDiagram.schur).coeff 3 = fourThirdCoefficient q P := by
  classical
  rw [four_marked_core hP]
  simp_rw [marked_generator_affine]
  rw [four_affine_coeff_three]
  have hA : (P.r 0 : ℤ) = q.val ↔ P.r 0 = q.val := by omega
  have hB : (P.r 1 : ℤ) = q.val ↔ P.r 1 = q.val := by omega
  have hC : (P.r 2 : ℤ) = q.val ↔ P.r 2 = q.val := by omega
  simp only [hA,hB,hC,indicator_triple,fourThirdCoefficient]

/-- Untouched restrictions already determine the full functions, including
the nonrotation full-four-row equalities. -/
theorem staircase_first_jet_untouched {n m : ℕ} {q : ℕ+} {P : Profile n} {Q : Profile m}
    (hcP : NoEntryContact q P) (hcQ : NoEntryContact q Q)
    (hzero : restriction q P = restriction q Q) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  rwa [restriction_eq_full_of_no_entry_contact hcP,
    restriction_eq_full_of_no_entry_contact hcQ] at hzero

private theorem four_core_degree (A B C U V X : Polynomial CompleteRing)
    (r s t d W Y T : CompleteRing)
    (hA : A.natDegree ≤ 1) (hB : B.natDegree ≤ 1) (hC : C.natDegree ≤ 1)
    (hU : U.natDegree ≤ 1) (hV : V.natDegree ≤ 1) (hX : X.natDegree ≤ 1) :
    (A*B*C*Polynomial.C d-U*Polynomial.C r*C*Polynomial.C d-
      A*V*Polynomial.C s*Polynomial.C d-A*B*Polynomial.C W*Polynomial.C t+
      X*Polynomial.C r*Polynomial.C s*Polynomial.C d+
      U*Polynomial.C r*Polynomial.C W*Polynomial.C t+
      A*Polynomial.C Y*Polynomial.C s*Polynomial.C t-
      Polynomial.C T*Polynomial.C r*Polynomial.C s*Polynomial.C t).natDegree ≤ 3 := by
  have hAB : (A*B).natDegree ≤ 2 := Polynomial.natDegree_mul_le_of_le hA hB
  have hABC : (A*B*C).natDegree ≤ 3 := Polynomial.natDegree_mul_le_of_le hAB hC
  have hUC : (U*Polynomial.C r*C).natDegree ≤ 2 :=
    Polynomial.natDegree_mul_le_of_le ((Polynomial.natDegree_mul_C_le _ _).trans hU) hC
  have hAV : (A*V).natDegree ≤ 2 := Polynomial.natDegree_mul_le_of_le hA hV
  have h1 : (A*B*C*Polynomial.C d).natDegree ≤ 3 :=
    (Polynomial.natDegree_mul_C_le _ _).trans hABC
  have h2 : (U*Polynomial.C r*C*Polynomial.C d).natDegree ≤ 3 :=
    (Polynomial.natDegree_mul_C_le _ _).trans (hUC.trans (by decide))
  have h3 : (A*V*Polynomial.C s*Polynomial.C d).natDegree ≤ 3 :=
    (Polynomial.natDegree_mul_C_le _ _).trans
      ((Polynomial.natDegree_mul_C_le _ _).trans (hAV.trans (by decide)))
  have h4 : (A*B*Polynomial.C W*Polynomial.C t).natDegree ≤ 3 :=
    (Polynomial.natDegree_mul_C_le _ _).trans
      ((Polynomial.natDegree_mul_C_le _ _).trans (hAB.trans (by decide)))
  have h5 : (X*Polynomial.C r*Polynomial.C s*Polynomial.C d).natDegree ≤ 3 :=
    (Polynomial.natDegree_mul_C_le _ _).trans
      ((Polynomial.natDegree_mul_C_le _ _).trans
        ((Polynomial.natDegree_mul_C_le _ _).trans (hX.trans (by decide))))
  have h6 : (U*Polynomial.C r*Polynomial.C W*Polynomial.C t).natDegree ≤ 3 :=
    (Polynomial.natDegree_mul_C_le _ _).trans
      ((Polynomial.natDegree_mul_C_le _ _).trans
        ((Polynomial.natDegree_mul_C_le _ _).trans (hU.trans (by decide))))
  have h7 : (A*Polynomial.C Y*Polynomial.C s*Polynomial.C t).natDegree ≤ 3 :=
    (Polynomial.natDegree_mul_C_le _ _).trans
      ((Polynomial.natDegree_mul_C_le _ _).trans
        ((Polynomial.natDegree_mul_C_le _ _).trans (hA.trans (by decide))))
  have h8 : (Polynomial.C T*Polynomial.C r*Polynomial.C s*Polynomial.C t).natDegree ≤ 3 := by
    simp only [← Polynomial.C_mul,Polynomial.natDegree_C]
    omega
  apply (Polynomial.natDegree_sub_le _ _).trans
  refine max_le ?_ h8
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · exact (Polynomial.natDegree_sub_le _ _).trans
          (max_le ((Polynomial.natDegree_sub_le _ _).trans
            (max_le ((Polynomial.natDegree_sub_le _ _).trans (max_le h1 h2)) h3)) h4)
      · exact h5
    · exact h6
  · exact h7

/-- The bottom row has degree zero in q, including its negative entries.
The actual determinant therefore has marked degree at most three. -/
theorem four_marked_degree_le_three {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    (minimumPolynomial q P.toBetaDiagram.schur).natDegree ≤ 3 := by
  rw [four_marked_core hP]
  apply four_core_degree
  all_goals split_ifs <;> simp

/-- All unknown coefficients after the first jet are exactly the two entries of
the collected four-row table.  No matching classification is assumed here. -/
theorem four_schur_eq_iff_jet_and_higher {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur ↔
      restriction q P = restriction q Q ∧
      firstCoefficient q P.toBetaDiagram.schur = firstCoefficient q Q.toBetaDiagram.schur ∧
      fourSecondCoefficient q P = fourSecondCoefficient q Q ∧
      fourThirdCoefficient q P = fourThirdCoefficient q Q := by
  constructor
  · intro he
    refine ⟨congrArg (eraseGenerator q) he, congrArg (firstCoefficient q) he, ?_, ?_⟩
    · have hh := congrArg (fun p : CompleteRing => (minimumPolynomial q p).coeff 2) he
      simpa only [four_marked_coeff_two hP, four_marked_coeff_two hQ] using hh
    · have hh := congrArg (fun p : CompleteRing => (minimumPolynomial q p).coeff 3) he
      simpa only [four_marked_coeff_three hP, four_marked_coeff_three hQ] using hh
  · rintro ⟨hzero, hone, htwo, hthree⟩
    apply minimumPolynomial_injective q
    apply Polynomial.ext
    intro k
    rcases k with _ | k
    · simpa only [minimumPolynomial_coeff_zero, restriction] using hzero
    rcases k with _ | k
    · change (minimumPolynomial q P.toBetaDiagram.schur).coeff 1 =
        (minimumPolynomial q Q.toBetaDiagram.schur).coeff 1
      simpa only [minimumPolynomial_coeff_one] using hone
    rcases k with _ | k
    · simpa only [four_marked_coeff_two hP, four_marked_coeff_two hQ] using htwo
    rcases k with _ | k
    · simpa only [four_marked_coeff_three hP, four_marked_coeff_three hQ] using hthree
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (four_marked_degree_le_three hP) (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (four_marked_degree_le_three hQ) (by omega))]

/-- Arbitrary-order mates of an at-most-three-row component are reduced by the
actual row-degree reading, then recovered from the actual first jet. -/
theorem staircase_first_jet_at_most_three {n m : ℕ} {q : ℕ+}
    {P : Profile n} {Q : Profile m} (hP : QComponent q P) (hQ : QComponent q Q)
    (hn : n ≤ 2) (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hnm := row_count_eq_of_restriction_eq hP hQ hzero
  subst m
  interval_cases n
  · exact staircase_first_jet_singleton hP hQ hzero
  · exact staircase_first_jet_two hP hQ hzero hone
  · exact staircase_first_jet_three hP hQ hzero hone

/-- The scalar marking retains every contact and is collected in the univariate ring. -/
noncomputable def scalarContactPolynomial (q a b c u v x : ℤ) : Polynomial ℚ :=
  let H (k : ℤ) : Polynomial ℚ := if k = q then Polynomial.X else 1
  H a * H b * H c - H u * H c - H a * H v - H a * H b +
    H x + H u + H a - 1

set_option maxHeartbeats 0 in
/-- The UC scalar pair is unique under the genuine interval order constraints. -/
theorem scalar_contact_uc_iff (q a b c u v x : ℤ)
    (hua : a < u) (hub : b < u) (hvb : b < v) (hvc : c < v)
    (hxu : u < x) (hxv : v < x) :
    ((scalarContactPolynomial q a b c u v x).coeff 0 = -1 ∧
      (scalarContactPolynomial q a b c u v x).coeff 1 = 2) ↔ u = q ∧ c = q := by
  classical
  dsimp [scalarContactPolynomial]
  split_ifs <;> norm_num [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, *] <;> omega

set_option maxHeartbeats 0 in
/-- The AV scalar pair is unique under the same actual interval order constraints. -/
theorem scalar_contact_av_iff (q a b c u v x : ℤ)
    (hua : a < u) (hub : b < u) (hvb : b < v) (hvc : c < v)
    (hxu : u < x) (hxv : v < x) :
    ((scalarContactPolynomial q a b c u v x).coeff 0 = 0 ∧
      (scalarContactPolynomial q a b c u v x).coeff 1 = 1) ↔ a = q ∧ v = q := by
  classical
  dsimp [scalarContactPolynomial]
  split_ifs <;> norm_num [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, *] <;> omega

/-- Actual scalar marking, obtained by mapping collected coefficients, not by
assuming that the surviving generators have different labels. -/
theorem four_scalar_marked {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    (minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation =
      scalarContactPolynomial q.val (P.r 0) (P.r 1) (P.r 2)
        ((P.r 0 : ℤ) + P.r 1 - P.g 0)
        ((P.r 1 : ℤ) + P.r 2 - P.g 1) (prefixIndex P) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hrow (i : Fin 4) := residualAugmentation_complete
    (show (0 : ℤ) < P.r i by exact_mod_cast P.r_pos i)
  have hgap (j : Fin 3) := residualAugmentation_complete
    (show (0 : ℤ) < P.g j by exact_mod_cast hP.gap_pos j)
  have hU := residualAugmentation_complete
    (show 0 < (P.r 0 : ℤ) + P.r 1 - P.g 0 by omega)
  have hV := residualAugmentation_complete
    (show 0 < (P.r 1 : ℤ) + P.r 2 - P.g 1 by omega)
  have hW := residualAugmentation_complete
    (show 0 < (P.r 2 : ℤ) + P.r 3 - P.g 2 by omega)
  have hX := residualAugmentation_complete
    (show 0 < prefixIndex P by dsimp [prefixIndex]; omega)
  have hY := residualAugmentation_complete
    (show 0 < suffixIndex P by dsimp [suffixIndex]; omega)
  have hT := residualAugmentation_complete P.toBetaDiagram.largestLabel_pos
  change residualAugmentation (complete (fullIndex P)) = 1 at hT
  rw [four_marked_core hP]
  dsimp only [scalarContactPolynomial]
  simp only [Polynomial.map_add,Polynomial.map_sub,Polynomial.map_mul,
    map_marked_atom _ _ (hrow 0),map_marked_atom _ _ (hrow 1),
    map_marked_atom _ _ (hrow 2),map_marked_atom _ _ hU,map_marked_atom _ _ hV,
    map_marked_atom _ _ hX,Polynomial.map_C,hrow,hgap,hW,hY,hT,
    Polynomial.C_1,one_mul,mul_one]

theorem four_scalar_uc_iff {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    (residualAugmentation (restriction q P) = -1 ∧
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) = 2) ↔
      (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 2 = q.val := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hzero : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 0 =
      residualAugmentation (restriction q P) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_zero, restriction]
  have hone : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 1 =
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_one]
  rw [← hzero, ← hone, four_scalar_marked hP]
  have hC : (P.r 2 : ℤ) = q.val ↔ P.r 2 = q.val := by omega
  simpa only [hC] using scalar_contact_uc_iff q.val (P.r 0) (P.r 1) (P.r 2)
    ((P.r 0 : ℤ) + P.r 1 - P.g 0) ((P.r 1 : ℤ) + P.r 2 - P.g 1) (prefixIndex P)
    (by omega) (by omega) (by omega) (by omega)
    (by dsimp [prefixIndex]; omega) (by dsimp [prefixIndex]; omega)

theorem four_scalar_av_iff {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    (residualAugmentation (restriction q P) = 0 ∧
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) = 1) ↔
      P.r 0 = q.val ∧ (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hzero : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 0 =
      residualAugmentation (restriction q P) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_zero, restriction]
  have hone : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 1 =
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_one]
  rw [← hzero, ← hone, four_scalar_marked hP]
  have hA : (P.r 0 : ℤ) = q.val ↔ P.r 0 = q.val := by omega
  simpa only [hA] using scalar_contact_av_iff q.val (P.r 0) (P.r 1) (P.r 2)
    ((P.r 0 : ℤ) + P.r 1 - P.g 0) ((P.r 1 : ℤ) + P.r 2 - P.g 1) (prefixIndex P)
    (by omega) (by omega) (by omega) (by omega)
    (by dsimp [prefixIndex]; omega) (by dsimp [prefixIndex]; omega)

/-- Exact UC first coefficient on the actual marked determinant. -/
theorem four_uc_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) (hc : P.r 2 = q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      complete (P.r 0) * complete (P.r 1) * complete (P.r 3) +
      complete (P.g 0) * complete (P.g 2) *
        complete ((q.val : ℤ) + P.r 3 - P.g 2) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hcc, hd⟩
  have hA : (P.r 0 : ℤ) ≠ q.val := by omega
  have hB : (P.r 1 : ℤ) ≠ q.val := by omega
  have hV : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  have hcq : (P.r 2 : ℤ) = q.val := by exact_mod_cast hc
  simp only [if_neg hA,if_neg hB,if_neg hV,if_neg hX,if_pos hu,if_pos hcq]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ]
  simp (failIfUnchanged := false) only [hc] <;> ring

/-- Exact AV first coefficient; no nonzero term is dropped at a coincident label. -/
theorem four_av_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hv : (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      complete (P.r 1) * complete (P.r 2) * complete (P.r 3) -
      complete (P.g 2) * complete (P.r 1) *
        complete ((P.r 2 : ℤ) + P.r 3 - P.g 2) +
      complete (P.g 1) * complete (P.g 2) *
        complete ((q.val : ℤ) + P.r 3 - P.g 2) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, hA, hb, hc, hd⟩
  have hB : (P.r 1 : ℤ) ≠ q.val := by omega
  have hC : (P.r 2 : ℤ) ≠ q.val := by omega
  have hU : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  have hY : suffixIndex P = (q.val : ℤ) + P.r 3 - P.g 2 := by dsimp [suffixIndex]; omega
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  have haq : (P.r 0 : ℤ) = q.val := by exact_mod_cast ha
  simp only [if_pos haq,if_neg hB,if_neg hC,if_neg hU,if_neg hX,if_pos hv,hY]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ]
  simp (failIfUnchanged := false) only [ha] <;> ring

theorem four_uc_higher_coefficients {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) (hc : P.r 2 = q.val) :
    fourSecondCoefficient q P = -complete (P.g 0) * complete (P.r 3) ∧
      fourThirdCoefficient q P = 0 := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hcc, hd⟩
  have hA : P.r 0 ≠ q.val := by omega
  have hB : P.r 1 ≠ q.val := by omega
  simp [fourSecondCoefficient, fourThirdCoefficient, hu, hc, hA, hB]

theorem four_av_higher_coefficients {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hv : (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val) :
    fourSecondCoefficient q P = -complete (P.g 1) * complete (P.r 3) ∧
      fourThirdCoefficient q P = 0 := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, hA, hb, hc, hd⟩
  have hB : P.r 1 ≠ q.val := by omega
  have hC : P.r 2 ≠ q.val := by omega
  simp [fourSecondCoefficient, fourThirdCoefficient, ha, hv, hB, hC]

/-- UC first-jet rigidity against an arbitrary actual four-row mate.
The scalar jet produces the mate's contact conditions before recovery. -/
theorem four_first_jet_uc {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) (hc : P.r 2 = q.val)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hsc := (four_scalar_uc_iff hP).mpr ⟨hu, hc⟩
  rw [hzero, hone] at hsc
  obtain ⟨hU, hC⟩ := (four_scalar_uc_iff hQ).mp hsc
  have hdom := P.four_domain hP.thick.hessenberg
  have hDOM := Q.four_domain hQ.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hcc, hd⟩
  rcases hDOM with ⟨hR, hS, hT, hA, hB, hCC, hD⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hBOTTOM : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have he := hone
  rw [four_uc_first_coefficient hP hu hc, four_uc_first_coefficient hQ hU hC] at he
  obtain ⟨hdd, htt, hrr⟩ := uc_first_coefficient_reading
    (by exact_mod_cast P.r_pos 0) (by exact_mod_cast P.r_pos 1)
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 2)
    (by exact_mod_cast Q.r_pos 0) (by exact_mod_cast Q.r_pos 1)
    (by exact_mod_cast hQ.gap_pos 0) (by exact_mod_cast hQ.gap_pos 2)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (by exact_mod_cast hbottom) (by exact_mod_cast hBOTTOM) he
  have hdNat : P.r 3 = Q.r 3 := by exact_mod_cast hdd
  have hrNat : P.g 0 = Q.g 0 := by exact_mod_cast hrr
  have hhighP := four_uc_higher_coefficients hP hu hc
  have hhighQ := four_uc_higher_coefficients hQ hU hC
  apply (four_schur_eq_iff_jet_and_higher hP hQ).mpr
  refine ⟨hzero, hone, ?_, ?_⟩
  · rw [hhighP.1, hhighQ.1, hdNat, hrNat]
  · rw [hhighP.2, hhighQ.2]

/-- AV first-jet rigidity against an arbitrary actual four-row mate, without
excluding collisions of the recovered linear factor with row or gap labels. -/
theorem four_first_jet_av {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 = q.val) (hv : (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hsc := (four_scalar_av_iff hP).mpr ⟨ha, hv⟩
  rw [hzero, hone] at hsc
  obtain ⟨hA, hV⟩ := (four_scalar_av_iff hQ).mp hsc
  have hdom := P.four_domain hP.thick.hessenberg
  have hDOM := Q.four_domain hQ.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb, hc, hd⟩
  rcases hDOM with ⟨hR, hS, hT, hA', hB, hC, hD⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hBOTTOM : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have he := hone
  rw [four_av_first_coefficient hP ha hv, four_av_first_coefficient hQ hA hV] at he
  obtain ⟨hbb, hcc, hdd, hss, htt⟩ := av_first_coefficient_reading
    (by exact_mod_cast P.r_pos 1) (by omega)
    (by exact_mod_cast hP.gap_pos 1) (by exact_mod_cast hP.gap_pos 2)
    (by exact_mod_cast Q.r_pos 1) (by omega)
    (by exact_mod_cast hQ.gap_pos 1) (by exact_mod_cast hQ.gap_pos 2)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (by exact_mod_cast hbottom) (by exact_mod_cast hBOTTOM) he
  have hdNat : P.r 3 = Q.r 3 := by exact_mod_cast hdd
  have hsNat : P.g 1 = Q.g 1 := by exact_mod_cast hss
  have hhighP := four_av_higher_coefficients hP ha hv
  have hhighQ := four_av_higher_coefficients hQ hA hV
  apply (four_schur_eq_iff_jet_and_higher hP hQ).mpr
  refine ⟨hzero, hone, ?_, ?_⟩
  · rw [hhighP.1, hhighQ.1, hdNat, hsNat]
  · rw [hhighP.2, hhighQ.2]

set_option maxHeartbeats 0 in
theorem scalar_contact_ac_bc_iff (q a b c u v x : ℤ)
    (hua : a < u) (hub : b < u) (hvb : b < v) (hvc : c < v)
    (hxu : u < x) (hxv : v < x) :
    ((scalarContactPolynomial q a b c u v x).coeff 0 = 1 ∧
      (scalarContactPolynomial q a b c u v x).coeff 1 = -2) ↔
      (a = q ∧ c = q ∧ b ≠ q) ∨ (b = q ∧ c = q ∧ a ≠ q) := by
  classical
  dsimp [scalarContactPolynomial]
  split_ifs <;> norm_num [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, *] <;> omega

theorem four_scalar_ac_bc_iff {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    (residualAugmentation (restriction q P) = 1 ∧
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) = -2) ↔
      (P.r 0 = q.val ∧ P.r 2 = q.val ∧ P.r 1 ≠ q.val) ∨
        (P.r 1 = q.val ∧ P.r 2 = q.val ∧ P.r 0 ≠ q.val) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hzero : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 0 =
      residualAugmentation (restriction q P) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_zero, restriction]
  have hone : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 1 =
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_one]
  rw [← hzero, ← hone, four_scalar_marked hP]
  have hA : (P.r 0 : ℤ) = q.val ↔ P.r 0 = q.val := by omega
  have hB : (P.r 1 : ℤ) = q.val ↔ P.r 1 = q.val := by omega
  have hC : (P.r 2 : ℤ) = q.val ↔ P.r 2 = q.val := by omega
  simpa only [hA,hB,hC,not_congr hA,not_congr hB,not_congr hC] using
    scalar_contact_ac_bc_iff q.val (P.r 0) (P.r 1) (P.r 2)
    ((P.r 0 : ℤ) + P.r 1 - P.g 0) ((P.r 1 : ℤ) + P.r 2 - P.g 1) (prefixIndex P)
    (by omega) (by omega) (by omega) (by omega)
    (by dsimp [prefixIndex]; omega) (by dsimp [prefixIndex]; omega)

theorem four_bc_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 ≠ q.val) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      -complete (P.g 0) * complete ((P.r 0 : ℤ) + q.val - P.g 0) * complete (P.r 3) -
        complete (P.g 2) * complete (P.r 0) *
          complete ((q.val : ℤ) + P.r 3 - P.g 2) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hA : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast ha
  have hU : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by omega
  have hV : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  have hbq : (P.r 1 : ℤ) = q.val := by exact_mod_cast hb
  have hcq : (P.r 2 : ℤ) = q.val := by exact_mod_cast hc
  simp only [if_neg hA,if_neg hU,if_neg hV,if_neg hX,if_pos hbq,if_pos hcq]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ]
  simp (failIfUnchanged := false) only [hb,hc] <;> ring

theorem four_ac_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hc : P.r 2 = q.val) (hb : P.r 1 ≠ q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      -complete (P.g 0) * complete ((q.val : ℤ) + P.r 1 - P.g 0) * complete (P.r 3) -
        complete (P.g 1) * complete ((q.val : ℤ) + P.r 1 - P.g 1) * complete (P.r 3) -
        complete (P.g 2) * complete (P.r 1) *
          complete ((q.val : ℤ) + P.r 3 - P.g 2) +
        complete (P.g 1) * complete (P.g 2) * complete (suffixIndex P) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hB : (P.r 1 : ℤ) ≠ q.val := by exact_mod_cast hb
  have hU : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by omega
  have hV : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  have haq : (P.r 0 : ℤ) = q.val := by exact_mod_cast ha
  have hcq : (P.r 2 : ℤ) = q.val := by exact_mod_cast hc
  simp only [if_neg hB,if_neg hU,if_neg hV,if_neg hX,if_pos haq,if_pos hcq]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ]
  simp (failIfUnchanged := false) only [ha,hc] <;> ring

theorem four_bc_first_derivative_nonpos {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 ≠ q.val) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val) (v : ℕ+) :
    residualAugmentation (MvPolynomial.pderiv v (firstCoefficient q P.toBetaDiagram.schur)) ≤ 0 := by
  rw [four_bc_first_coefficient hP ha hb hc]
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have he : -complete (P.g 0) * complete ((P.r 0 : ℤ) + q.val - P.g 0) * complete (P.r 3) -
      complete (P.g 2) * complete (P.r 0) * complete ((q.val : ℤ) + P.r 3 - P.g 2) =
    -(complete (P.g 0) * complete ((P.r 0 : ℤ) + q.val - P.g 0) * complete (P.r 3)) -
      complete (P.g 2) * complete (P.r 0) * complete ((q.val : ℤ) + P.r 3 - P.g 2) := by ring
  rw [he]
  exact negative_triple_pair_derivative_nonpos _ _ _ _ _ _
    (by exact_mod_cast hP.gap_pos 0) (by omega) (by exact_mod_cast P.r_pos 3)
    (by exact_mod_cast hP.gap_pos 2) (by exact_mod_cast P.r_pos 0) (by omega) v

/-- The positive AC derivative distinguishes the two contacts sharing one scalar jet. -/
theorem four_ac_first_positive_derivative {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hc : P.r 2 = q.val) (hb : P.r 1 ≠ q.val) :
    ∃ v : ℕ+, residualAugmentation
      (MvPolynomial.pderiv v (firstCoefficient q P.toBetaDiagram.schur)) = 1 := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hy : 0 < suffixIndex P := by dsimp [suffixIndex]; omega
  let v : ℕ+ := ⟨(suffixIndex P).toNat, by omega⟩
  have hv : (v.val : ℤ) = suffixIndex P := by dsimp [v]; omega
  refine ⟨v, ?_⟩
  rw [four_ac_first_coefficient hP ha hc hb]
  have hY : suffixIndex P = (P.r 1 : ℤ) + q.val + P.r 3 - P.g 1 - P.g 2 := by
    dsimp [suffixIndex]
    rw [hc]
  rw [hY]
  rw [ac_first_coefficient_top q.val (P.r 1) (P.r 3) (P.g 0) (P.g 1) (P.g 2)
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
    (by exact_mod_cast hP.gap_pos 2) (by omega) (by omega)
    (by omega) (by exact_mod_cast hbottom) v (hv.trans hY)]
  simp only [map_mul,
    residualAugmentation_complete (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1),
    residualAugmentation_complete (show (0 : ℤ) < P.g 2 by exact_mod_cast hP.gap_pos 2),
    one_mul]

theorem four_bc_higher_coefficients {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 ≠ q.val) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val) :
    fourSecondCoefficient q P = complete (P.r 0) * complete (P.r 3) ∧
      fourThirdCoefficient q P = 0 := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hU : (P.r 0 : ℤ)+q.val-P.g 0 ≠ q.val := by omega
  simp [fourSecondCoefficient, fourThirdCoefficient, ha, hb, hc, hU,
    bar_eq_complete_of_ne q (P.r 0) (by exact_mod_cast ha)]

/-- BC first-jet rigidity, with the AC competitor excluded by the sign of
its private first-coefficient derivative, not by a residual classification. -/
theorem four_first_jet_bc {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 ≠ q.val) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hsc := (four_scalar_ac_bc_iff hP).mpr (Or.inr ⟨hb, hc, ha⟩)
  rw [hzero, hone] at hsc
  rcases (four_scalar_ac_bc_iff hQ).mp hsc with ⟨hA, hC, hB⟩ | ⟨hB, hC, hA⟩
  · obtain ⟨v, hpos⟩ := four_ac_first_positive_derivative hQ hA hC hB
    have hnon := four_bc_first_derivative_nonpos hP ha hb hc v
    rw [hone, hpos] at hnon
    norm_num at hnon
  · have hdom := P.four_domain hP.thick.hessenberg
    have hDOM := Q.four_domain hQ.thick.hessenberg
    rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
    rcases hDOM with ⟨hR, hS, hT, hA', hB', hC', hD⟩
    have hbottom : q.val + P.g 2 < P.r 3 := by
      simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
    have hBOTTOM : q.val + Q.g 2 < Q.r 3 := by
      simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
    have he : complete (P.g 0) * complete ((P.r 0 : ℤ) + q.val - P.g 0) * complete (P.r 3) +
        complete (P.g 2) * complete (P.r 0) * complete ((q.val : ℤ) + P.r 3 - P.g 2) =
      complete (Q.g 0) * complete ((Q.r 0 : ℤ) + q.val - Q.g 0) * complete (Q.r 3) +
        complete (Q.g 2) * complete (Q.r 0) * complete ((q.val : ℤ) + Q.r 3 - Q.g 2) := by
      rw [four_bc_first_coefficient hP ha hb hc, four_bc_first_coefficient hQ hA hB hC] at hone
      linear_combination -hone
    have hrows := bc_endpoint_product_reading q.val (P.r 0) (P.r 3) (P.g 0) (P.g 2)
      (Q.r 0) (Q.r 3) (Q.g 0) (Q.g 2)
      (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 2)
      (by omega) (by omega) ha' (by exact_mod_cast hbottom) (by exact_mod_cast ha)
      (by exact_mod_cast hQ.gap_pos 0) (by exact_mod_cast hQ.gap_pos 2)
      (by omega) (by omega) hA' (by exact_mod_cast hBOTTOM) (by exact_mod_cast hA) he
    have hprod : complete (P.r 0) * complete (P.r 3) =
        complete (Q.r 0) * complete (Q.r 3) := by
      rcases hrows with ⟨hae, hde⟩ | ⟨hae, hde⟩
      · rw [hae, hde]
      · rw [hae, hde]; ring
    have hhighP := four_bc_higher_coefficients hP ha hb hc
    have hhighQ := four_bc_higher_coefficients hQ hA hB hC
    apply (four_schur_eq_iff_jet_and_higher hP hQ).mpr
    refine ⟨hzero, hone, ?_, ?_⟩
    · rw [hhighP.1, hhighQ.1, hprod]
    · rw [hhighP.2, hhighQ.2]

theorem four_ac_restriction {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hc : P.r 2 = q.val) :
    restriction q P = -complete (P.g 0) *
      middleContactCubic q.val ((q.val : ℤ) + P.r 1 - P.g 0)
        (P.r 3) (P.g 1) (P.g 2) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb, hc', hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  rw [restriction_four_first_row_cut P hP.thick ha]
  simp only [ha, hc, threeInterval, bar_cut, mul_zero, zero_mul, zero_sub]
  rw [bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1),
    bar_eq_complete_of_ne q (P.g 2) (by exact_mod_cast hP.gap_ne 2),
    bar_eq_complete_of_ne q (P.r 3) (by omega),
    bar_eq_complete_of_ne q _ (by omega),
    bar_eq_complete_of_ne q _ (by omega),
    bar_eq_complete_of_ne q _ (by omega),
    bar_eq_complete_of_ne q _ (by omega)]
  unfold middleContactCubic
  ring

theorem four_ac_higher_coefficients {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hc : P.r 2 = q.val) (hb : P.r 1 ≠ q.val) :
    fourSecondCoefficient q P = complete (P.r 1) * complete (P.r 3) ∧
      fourThirdCoefficient q P = 0 := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hU : (q.val : ℤ)+P.r 1-P.g 0 ≠ q.val := by omega
  have hV : (P.r 1 : ℤ)+q.val-P.g 1 ≠ q.val := by omega
  simp [fourSecondCoefficient, fourThirdCoefficient, ha, hb, hc, hU, hV,
    bar_eq_complete_of_ne q (P.r 1) (by exact_mod_cast hb)]

/-- Same-contact AC recovery, including equal contracted gaps and both
orientations of the contracted profile. -/
theorem four_first_jet_ac_pair {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 = q.val) (hc : P.r 2 = q.val) (hb : P.r 1 ≠ q.val)
    (hA : Q.r 0 = q.val) (hC : Q.r 2 = q.val) (hB : Q.r 1 ≠ q.val)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hdom := P.four_domain hP.thick.hessenberg
  have hDOM := Q.four_domain hQ.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  rcases hDOM with ⟨hR, hS, hT, hA', hB', hC', hD⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hBOTTOM : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have hYp : suffixIndex P = (P.r 1 : ℤ) + q.val + P.r 3 - P.g 1 - P.g 2 := by
    dsimp [suffixIndex]; rw [hc]
  have hYq : suffixIndex Q = (Q.r 1 : ℤ) + q.val + Q.r 3 - Q.g 1 - Q.g 2 := by
    dsimp [suffixIndex]; rw [hC]
  have hjet := hone
  rw [four_ac_first_coefficient hP ha hc hb,
    four_ac_first_coefficient hQ hA hC hB, hYp, hYq] at hjet
  have hpeak := ac_first_coefficient_largest q.val (P.r 1) (P.r 3)
    (P.g 0) (P.g 1) (P.g 2) (Q.r 1) (Q.r 3) (Q.g 0) (Q.g 1) (Q.g 2)
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
    (by exact_mod_cast hP.gap_pos 2) (by omega) (by omega) hb'
    (by exact_mod_cast hbottom)
    (by exact_mod_cast hQ.gap_pos 0) (by exact_mod_cast hQ.gap_pos 1)
    (by exact_mod_cast hQ.gap_pos 2) (by omega) (by omega) hB'
    (by exact_mod_cast hBOTTOM) hjet
  have hfull := (restriction_full_and_gap_eq hP hQ hzero).1
  have hrR : P.g 0 = Q.g 0 := by
    rw [fullIndex_four, fullIndex_four] at hfull
    simp only [ha, hc, hA, hC] at hfull
    have hy := hpeak.1
    omega
  have hmid : middleContactCubic q.val ((q.val : ℤ) + P.r 1 - P.g 0)
      (P.r 3) (P.g 1) (P.g 2) =
    middleContactCubic q.val ((q.val : ℤ) + Q.r 1 - Q.g 0)
      (Q.r 3) (Q.g 1) (Q.g 2) := by
    have he := hzero
    rw [four_ac_restriction hP ha hc, four_ac_restriction hQ hA hC, hrR] at he
    rw [hrR]
    exact mul_left_cancel₀
      (neg_ne_zero.mpr ((complete_ne_zero_iff (Q.g 0)).mpr (by positivity))) he
  have hrows := middleContactCubic_rigidity q.val
    ((q.val : ℤ) + P.r 1 - P.g 0) (P.r 3) (P.g 1) (P.g 2)
    ((q.val : ℤ) + Q.r 1 - Q.g 0) (Q.r 3) (Q.g 1) (Q.g 2)
    (by exact_mod_cast hP.gap_pos 1) (by exact_mod_cast hP.gap_pos 2)
    (by omega) (by omega) (by exact_mod_cast hbottom)
    (by exact_mod_cast hQ.gap_pos 1) (by exact_mod_cast hQ.gap_pos 2)
    (by omega) (by omega) (by exact_mod_cast hBOTTOM) hmid
  have hprod : complete (P.r 1) * complete (P.r 3) =
      complete (Q.r 1) * complete (Q.r 3) := by
    rcases hrows with ⟨hU, hdd, hss, htt⟩ | ⟨hU, hdd, hst, hts⟩
    · have hbb : P.r 1 = Q.r 1 := by omega
      have hddNat : P.r 3 = Q.r 3 := by exact_mod_cast hdd
      rw [hbb, hddNat]
    · have hstNat : P.g 1 = Q.g 2 := by exact_mod_cast hst
      have htsNat : P.g 2 = Q.g 1 := by exact_mod_cast hts
      have hfirst : complete (P.g 0) * complete ((q.val : ℤ) + P.r 1 - P.g 0) *
          complete (P.r 3) =
        complete (Q.g 0) * complete ((q.val : ℤ) + Q.r 1 - Q.g 0) *
          complete (Q.r 3) := by
        have hdlift : (P.r 3 : ℤ) = (q.val : ℤ) + Q.r 1 - P.g 0 := by
          rw [hrR]
          exact hdd
        rw [← hrR, hU, ← hdlift]
        ring
      have hlead := congrArg
        (fun p : CompleteRing =>
          p * complete ((Q.r 1 : ℤ) + q.val + Q.r 3 - Q.g 1 - Q.g 2)) hpeak.2
      have htail : complete (P.g 1) * complete ((q.val : ℤ) + P.r 1 - P.g 1) *
          complete (P.r 3) +
          complete (P.g 2) * complete (P.r 1) * complete ((q.val : ℤ) + P.r 3 - P.g 2) =
        complete (P.g 2) * complete ((q.val : ℤ) + Q.r 1 - P.g 2) * complete (Q.r 3) +
          complete (P.g 1) * complete (Q.r 1) * complete ((q.val : ℤ) + Q.r 3 - P.g 1) := by
        have he := hjet
        rw [hpeak.1] at he
        rw [← htsNat, ← hstNat] at he hlead
        linear_combination -he - hfirst + hlead
      obtain ⟨hbb, hdd', hst'⟩ := ac_rotated_tail_reading q.val (P.g 0) (P.g 1) (P.g 2)
        (P.r 1) (P.r 3) (Q.r 1) (Q.r 3)
        (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
        (by exact_mod_cast hP.gap_pos 2) (by omega) (by omega) hb'
        (by rw [hrR, htsNat]; exact hB')
        (by exact_mod_cast hbottom)
        (by rw [hstNat]; exact_mod_cast hBOTTOM)
        (by exact_mod_cast hb) (by exact_mod_cast hB)
        hU.symm (by rw [hrR]; exact hdd) htail
      rw [hbb, hdd']
  have hhighP := four_ac_higher_coefficients hP ha hc hb
  have hhighQ := four_ac_higher_coefficients hQ hA hC hB
  apply (four_schur_eq_iff_jet_and_higher hP hQ).mpr
  refine ⟨hzero, hone, ?_, ?_⟩
  · rw [hhighP.1, hhighQ.1, hprod]
  · rw [hhighP.2, hhighQ.2]

/-- AC first-jet rigidity against every four-row mate; the BC competitor is
excluded by its nonpositive derivative coefficients. -/
theorem four_first_jet_ac {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 = q.val) (hc : P.r 2 = q.val) (hb : P.r 1 ≠ q.val)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hsc := (four_scalar_ac_bc_iff hP).mpr (Or.inl ⟨ha, hc, hb⟩)
  rw [hzero, hone] at hsc
  rcases (four_scalar_ac_bc_iff hQ).mp hsc with ⟨hA, hC, hB⟩ | ⟨hB, hC, hA⟩
  · exact four_first_jet_ac_pair hP hQ ha hc hb hA hC hB hzero hone
  · obtain ⟨v, hpos⟩ := four_ac_first_positive_derivative hP ha hc hb
    have hnon := four_bc_first_derivative_nonpos hQ hA hB hC v
    rw [← hone, hpos] at hnon
    norm_num at hnon

set_option maxHeartbeats 0 in
theorem scalar_contact_abc_v_iff (q a b c u v x : ℤ)
    (hua : a < u) (hub : b < u) (hvb : b < v) (hvc : c < v)
    (hxu : u < x) (hxv : v < x) :
    ((scalarContactPolynomial q a b c u v x).coeff 0 = 1 ∧
      (scalarContactPolynomial q a b c u v x).coeff 1 = -1) ↔
      (a = q ∧ b = q ∧ c = q) ∨ (v = q ∧ a ≠ q) := by
  classical
  dsimp [scalarContactPolynomial]
  split_ifs <;> norm_num [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, *] <;> omega

theorem four_scalar_abc_v_iff {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    (residualAugmentation (restriction q P) = 1 ∧
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) = -1) ↔
      (P.r 0 = q.val ∧ P.r 1 = q.val ∧ P.r 2 = q.val) ∨
        ((P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val ∧ P.r 0 ≠ q.val) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hzero : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 0 =
      residualAugmentation (restriction q P) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_zero, restriction]
  have hone : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 1 =
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_one]
  rw [← hzero, ← hone, four_scalar_marked hP]
  have hA : (P.r 0 : ℤ) = q.val ↔ P.r 0 = q.val := by omega
  have hB : (P.r 1 : ℤ) = q.val ↔ P.r 1 = q.val := by omega
  have hC : (P.r 2 : ℤ) = q.val ↔ P.r 2 = q.val := by omega
  simpa only [hA,hB,hC,not_congr hA,not_congr hB,not_congr hC] using
    scalar_contact_abc_v_iff q.val (P.r 0) (P.r 1) (P.r 2)
    ((P.r 0 : ℤ) + P.r 1 - P.g 0) ((P.r 1 : ℤ) + P.r 2 - P.g 1) (prefixIndex P)
    (by omega) (by omega) (by omega) (by omega)
    (by dsimp [prefixIndex]; omega) (by dsimp [prefixIndex]; omega)

theorem four_abc_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      abcFirstPolynomial q.val (P.r 3) (P.g 0) (P.g 1) (P.g 2) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hU : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by omega
  have hV : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  have hY : suffixIndex P = 2 * (q.val : ℤ) + P.r 3 - P.g 1 - P.g 2 := by
    dsimp [suffixIndex]; rw [hb, hc]; ring
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  have haq : (P.r 0 : ℤ) = q.val := by exact_mod_cast ha
  have hbq : (P.r 1 : ℤ) = q.val := by exact_mod_cast hb
  have hcq : (P.r 2 : ℤ) = q.val := by exact_mod_cast hc
  simp only [if_neg hU,if_neg hV,if_neg hX,if_pos haq,if_pos hbq,if_pos hcq,hY]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ]
  simp (failIfUnchanged := false) only [ha,hb,hc]
  unfold abcFirstPolynomial
  have h1 : (q.val : ℤ) + q.val - P.g 0 = 2 * q.val - P.g 0 := by ring
  have h2 : (q.val : ℤ) + q.val - P.g 1 = 2 * q.val - P.g 1 := by ring
  rw [h1, h2]
  ring

theorem four_v_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (hv : (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val) (ha : P.r 0 ≠ q.val)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      -(complete (P.g 1) * complete (P.r 0) * complete (P.r 3)) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb, hc, hd⟩
  have hA : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast ha
  have hB : (P.r 1 : ℤ) ≠ q.val := by omega
  have hC : (P.r 2 : ℤ) ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  simp only [if_neg hA, if_neg hB, if_neg hC, if_neg hu, if_neg hX, if_pos hv]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ] <;>
    ring <;> exact Or.inl trivial

theorem four_uv_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val)
    (hv : (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      uvFirstPolynomial (P.r 0) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hA : (P.r 0 : ℤ) ≠ q.val := by omega
  have hB : (P.r 1 : ℤ) ≠ q.val := by omega
  have hC : (P.r 2 : ℤ) ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  simp only [if_neg hA, if_neg hB, if_neg hC, if_neg hX, if_pos hu, if_pos hv]
  norm_num [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
  unfold uvFirstPolynomial
  ring

theorem four_abc_higher_coefficients {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val) :
    fourSecondCoefficient q P =
      -complete (P.g 2) * complete ((q.val : ℤ) + P.r 3 - P.g 2) ∧
      fourThirdCoefficient q P = complete (P.r 3) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hU : (q.val : ℤ)+q.val-P.g 0 ≠ q.val := by omega
  have hV : (q.val : ℤ)+q.val-P.g 1 ≠ q.val := by omega
  simp [fourSecondCoefficient, fourThirdCoefficient, ha, hb, hc, hU, hV]

theorem four_abc_first_positive_derivative {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val) :
    ∃ v : ℕ+, residualAugmentation
      (MvPolynomial.pderiv v (firstCoefficient q P.toBetaDiagram.schur)) = 1 := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  let k : ℤ := 2 * q.val + P.r 3 - P.g 1 - P.g 2
  have hk : 0 < k := by dsimp [k]; omega
  let v : ℕ+ := ⟨k.toNat, by omega⟩
  have hv : (v.val : ℤ) = k := by dsimp [v]; omega
  refine ⟨v, ?_⟩
  rw [four_abc_first_coefficient hP ha hb hc]
  rw [abc_first_top q.val (P.r 3) (P.g 0) (P.g 1) (P.g 2)
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
    (by exact_mod_cast hP.gap_pos 2) (by omega) (by omega)
    (by exact_mod_cast hbottom) v hv]
  simp only [map_mul,
    residualAugmentation_complete (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1),
    residualAugmentation_complete (show (0 : ℤ) < P.g 2 by exact_mod_cast hP.gap_pos 2),
    one_mul]

/-- Paired ABC recovery uses full-interval and repeated-gap readings, then the
private positive first-coefficient term and one oriented binomial monomial. -/
theorem four_first_jet_abc_pair {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val)
    (hA : Q.r 0 = q.val) (hB : Q.r 1 = q.val) (hC : Q.r 2 = q.val)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hdom := P.four_domain hP.thick.hessenberg
  have hDOM := Q.four_domain hQ.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  rcases hDOM with ⟨hR, hS, hT, hA', hB', hC', hD⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hBOTTOM : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  obtain ⟨hfull, hgap⟩ := restriction_full_and_gap_eq hP hQ hzero
  have hsum := gap_sum_three_eq hP hQ hgap
  have hdD : P.r 3 = Q.r 3 := by
    rw [fullIndex_four, fullIndex_four] at hfull
    simp only [ha, hb, hc, hA, hB, hC] at hfull
    omega
  have hjet := hone
  rw [four_abc_first_coefficient hP ha hb hc, four_abc_first_coefficient hQ hA hB hC] at hjet
  have hpeak := abc_first_largest q.val (P.r 3) (P.g 0) (P.g 1) (P.g 2)
    (Q.r 3) (Q.g 0) (Q.g 1) (Q.g 2)
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
    (by exact_mod_cast hP.gap_pos 2) (by omega) (by omega) (by exact_mod_cast hbottom)
    (by exact_mod_cast hQ.gap_pos 0) (by exact_mod_cast hQ.gap_pos 1)
    (by exact_mod_cast hQ.gap_pos 2) (by omega) (by omega) (by exact_mod_cast hBOTTOM) hjet
  have hrR : P.g 0 = Q.g 0 := by have hy := hpeak.1; omega
  have hneg : complete (P.g 1) * complete (2 * (q.val : ℤ) - P.g 1) * complete (P.r 3) =
      complete (Q.g 1) * complete (2 * (q.val : ℤ) - Q.g 1) * complete (Q.r 3) := by
    have he := hjet
    unfold abcFirstPolynomial at he
    rw [hpeak.1] at he
    have hfirst : complete (P.g 0) * complete (2 * (q.val : ℤ) - P.g 0) * complete (P.r 3) =
        complete (Q.g 0) * complete (2 * (q.val : ℤ) - Q.g 0) * complete (Q.r 3) := by
      rw [hrR, hdD]
    have hlead := congrArg
      (fun p : CompleteRing => p * complete (2 * (q.val : ℤ) + Q.r 3 - Q.g 1 - Q.g 2)) hpeak.2
    linear_combination -he - hfirst + hlead
  rw [hdD] at hneg
  have hpair := mul_right_cancel₀
    ((complete_ne_zero_iff (Q.r 3)).mpr (by positivity)) hneg
  have hmon := complete_two_product_reading
    (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1)
    (show 0 < 2 * (q.val : ℤ) - P.g 1 by omega)
    (show (0 : ℤ) < Q.g 1 by exact_mod_cast hQ.gap_pos 1)
    (show 0 < 2 * (q.val : ℤ) - Q.g 1 by omega) hpair
  have hsS : P.g 1 = Q.g 1 := by
    rcases hmon with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have htT : P.g 2 = Q.g 2 := by have hy := hpeak.1; omega
  have hhighP := four_abc_higher_coefficients hP ha hb hc
  have hhighQ := four_abc_higher_coefficients hQ hA hB hC
  apply (four_schur_eq_iff_jet_and_higher hP hQ).mpr
  refine ⟨hzero, hone, ?_, ?_⟩
  · rw [hhighP.1, hhighQ.1, hdD, htT]
  · rw [hhighP.2, hhighQ.2, hdD]

/-- ABC first-jet rigidity against every four-row mate, including the V/UV
competitors with the same scalar jet. -/
theorem four_first_jet_abc {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hsc := (four_scalar_abc_v_iff hP).mpr (Or.inl ⟨ha, hb, hc⟩)
  rw [hzero, hone] at hsc
  rcases (four_scalar_abc_v_iff hQ).mp hsc with ⟨hA, hB, hC⟩ | ⟨hV, hA⟩
  · exact four_first_jet_abc_pair hP hQ ha hb hc hA hB hC hzero hone
  · have hdom := P.four_domain hP.thick.hessenberg
    have hDOM := Q.four_domain hQ.thick.hessenberg
    rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
    rcases hDOM with ⟨hR, hS, hT, hA', hB', hC', hD⟩
    have hbottom : q.val + P.g 2 < P.r 3 := by
      simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
    have hBOTTOM : q.val + Q.g 2 < Q.r 3 := by
      simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
    by_cases hU : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = q.val
    · have he := hone
      rw [four_abc_first_coefficient hP ha hb hc, four_uv_first_coefficient hQ hU hV] at he
      exact (abc_uv_first_ne q.val (P.r 3) (P.g 0) (P.g 1) (P.g 2)
        (Q.r 0) (Q.r 2) (Q.r 3) (Q.g 0) (Q.g 1) (Q.g 2)
        (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
        (by exact_mod_cast hP.gap_pos 2) (by omega) (by omega) (by omega)
        (by exact_mod_cast hbottom)
        (by exact_mod_cast Q.r_pos 0) (by exact_mod_cast Q.r_pos 2)
        (by exact_mod_cast hQ.gap_pos 0) (by exact_mod_cast hQ.gap_pos 1)
        (by exact_mod_cast hQ.gap_pos 2) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by exact_mod_cast Q.g_lt_castSucc 2) (by exact_mod_cast hBOTTOM) he).elim
    · obtain ⟨v, hpos⟩ := four_abc_first_positive_derivative hP ha hb hc
      have hnon := negative_triple_derivative_nonpos (Q.g 1) (Q.r 0) (Q.r 3)
        (by exact_mod_cast hQ.gap_pos 1) (by exact_mod_cast Q.r_pos 0)
        (by exact_mod_cast Q.r_pos 3) v
      rw [← four_v_first_coefficient hQ hV hA hU, ← hone, hpos] at hnon
      norm_num at hnon

set_option maxHeartbeats 0 in
theorem scalar_zero_contact_cases (q a b c u v x : ℤ)
    (hua : a < u) (hub : b < u) (hvb : b < v) (hvc : c < v)
    (hxu : u < x) (hxv : v < x)
    (hjet : (scalarContactPolynomial q a b c u v x).coeff 0 = 0 ∧
      (scalarContactPolynomial q a b c u v x).coeff 1 = 0) :
    (a ≠ q ∧ b ≠ q ∧ c ≠ q ∧ u ≠ q ∧ v ≠ q ∧ x ≠ q) ∨
    (a = q ∧ b ≠ q ∧ c ≠ q ∧ v ≠ q) ∨
    (b = q ∧ a ≠ q ∧ c ≠ q) ∨
    (c = q ∧ a ≠ q ∧ b ≠ q ∧ u ≠ q) ∨
    (u = q ∧ c ≠ q ∧ v ≠ q) ∨
    (a = q ∧ b = q ∧ c ≠ q) := by
  classical
  dsimp [scalarContactPolynomial] at hjet
  split_ifs at hjet <;>
    norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ, *] at hjet <;> omega

theorem four_scalar_zero_contact_cases {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (hjet : residualAugmentation (restriction q P) = 0 ∧
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) = 0) :
    NoEntryContact q P ∨
    (P.r 0 = q.val ∧ P.r 1 ≠ q.val ∧ P.r 2 ≠ q.val ∧
      (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val) ∨
    (P.r 1 = q.val ∧ P.r 0 ≠ q.val ∧ P.r 2 ≠ q.val) ∨
    (P.r 2 = q.val ∧ P.r 0 ≠ q.val ∧ P.r 1 ≠ q.val ∧
      (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val) ∨
    ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 2 ≠ q.val ∧
      (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val) ∨
    (P.r 0 = q.val ∧ P.r 1 = q.val ∧ P.r 2 ≠ q.val) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hzero : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 0 =
      residualAugmentation (restriction q P) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_zero, restriction]
  have hone : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 1 =
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_one]
  rw [← hzero, ← hone, four_scalar_marked hP] at hjet
  have hcases := scalar_zero_contact_cases q.val (P.r 0) (P.r 1) (P.r 2)
    ((P.r 0 : ℤ) + P.r 1 - P.g 0) ((P.r 1 : ℤ) + P.r 2 - P.g 1) (prefixIndex P)
    (by omega) (by omega) (by omega) (by omega)
    (by dsimp [prefixIndex]; omega) (by dsimp [prefixIndex]; omega) hjet
  have hA : (P.r 0 : ℤ) = q.val ↔ P.r 0 = q.val := by omega
  have hB : (P.r 1 : ℤ) = q.val ↔ P.r 1 = q.val := by omega
  have hC : (P.r 2 : ℤ) = q.val ↔ P.r 2 = q.val := by omega
  simp only [hA,hB,hC,not_congr hA,not_congr hB,not_congr hC] at hcases
  rcases hcases with ⟨ha', hb', hc', hu, hv, hx⟩ | h | h | h | h | h
  · exact Or.inl (four_no_contact_of_first_indices hP ha' hb' hc' hu hv hx)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem minimumPolynomial_constant_of_no_contact {n : ℕ} {q : ℕ+} {P : Profile n}
    (hc : NoEntryContact q P) :
    minimumPolynomial q P.toBetaDiagram.schur = Polynomial.C P.toBetaDiagram.schur := by
  rw [BetaDiagram.schur, (minimumPolynomial q).map_det,
    (Polynomial.C : CompleteRing →+* Polynomial CompleteRing).map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change minimumPolynomial q (complete (P.xi i - P.zeta j)) =
    Polynomial.C (complete (P.xi i - P.zeta j))
  exact minimumPolynomial_complete_ne q _ (hc i j)

theorem firstCoefficient_zero_of_no_contact {n : ℕ} {q : ℕ+} {P : Profile n}
    (hc : NoEntryContact q P) : firstCoefficient q P.toBetaDiagram.schur = 0 := by
  rw [← minimumPolynomial_coeff_one, minimumPolynomial_constant_of_no_contact hc]
  simp

theorem four_ab_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 ≠ q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      complete (P.g 1) * quadraticB (P.g 2)
        ((q.val : ℤ) + P.r 2 - P.g 1) (P.r 3) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hC : (P.r 2 : ℤ) ≠ q.val := by exact_mod_cast hc
  have hU : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by omega
  have hV : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  have hY : suffixIndex P = (q.val : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 := by
    dsimp [suffixIndex]; rw [hb]
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  have haq : (P.r 0 : ℤ) = q.val := by exact_mod_cast ha
  have hbq : (P.r 1 : ℤ) = q.val := by exact_mod_cast hb
  simp only [if_neg hC,if_neg hU,if_neg hV,if_neg hX,if_pos haq,if_pos hbq,hY]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ]
  simp (failIfUnchanged := false) only [ha,hb]
  unfold quadraticB
  have hidx : (q.val : ℤ) + P.r 2 - P.g 1 + P.r 3 - P.g 2 =
      (q.val : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 := by ring
  rw [hidx]
  ring

theorem four_ab_higher_coefficients {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 ≠ q.val) :
    fourSecondCoefficient q P = -quadraticB (P.g 2) (P.r 2) (P.r 3) ∧
      fourThirdCoefficient q P = 0 := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hU : (q.val : ℤ)+q.val-P.g 0 ≠ q.val := by omega
  have hV : (q.val : ℤ)+P.r 2-P.g 1 ≠ q.val := by omega
  constructor <;>
    simp [fourSecondCoefficient,fourThirdCoefficient,ha,hb,hc,hU,hV,
      bar_eq_complete_of_ne q (P.r 2) (by exact_mod_cast hc),quadraticB] <;> ring

theorem four_b_only_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (hb : P.r 1 = q.val) (ha : P.r 0 ≠ q.val) (hc : P.r 2 ≠ q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      -(complete (P.r 0) * quadraticB (P.g 2) (P.r 2) (P.r 3)) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hA : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast ha
  have hC : (P.r 2 : ℤ) ≠ q.val := by exact_mod_cast hc
  have hU : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by omega
  have hV : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  have hbq : (P.r 1 : ℤ) = q.val := by exact_mod_cast hb
  simp only [if_neg hA,if_neg hC,if_neg hU,if_neg hV,if_neg hX,if_pos hbq]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ]
  simp (failIfUnchanged := false) only [hb]
  unfold quadraticB
  ring

theorem four_c_only_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (hc : P.r 2 = q.val) (ha : P.r 0 ≠ q.val) (hb : P.r 1 ≠ q.val)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      -(complete (P.r 3) * quadraticB (P.g 0) (P.r 0) (P.r 1)) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hA : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast ha
  have hB : (P.r 1 : ℤ) ≠ q.val := by exact_mod_cast hb
  have hV : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  have hcq : (P.r 2 : ℤ) = q.val := by exact_mod_cast hc
  simp only [if_neg hA,if_neg hB,if_neg hu,if_neg hV,if_neg hX,if_pos hcq]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ]
  simp (failIfUnchanged := false) only [hc]
  unfold quadraticB
  ring

theorem four_u_only_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) (hc : P.r 2 ≠ q.val)
    (hv : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      complete (P.g 0) * quadraticB (P.g 2) (P.r 2) (P.r 3) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc', hd⟩
  have hA : (P.r 0 : ℤ) ≠ q.val := by omega
  have hB : (P.r 1 : ℤ) ≠ q.val := by omega
  have hC : (P.r 2 : ℤ) ≠ q.val := by exact_mod_cast hc
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  rw [← minimumPolynomial_coeff_one, four_marked_core hP]
  simp only [if_neg hA, if_neg hB, if_neg hC, if_neg hv, if_neg hX, if_pos hu]
  norm_num [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
  unfold quadraticB
  ring


theorem suffix_three_component {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    QComponent q (GeneralHessenberg.slice P 1 2 (by decide)) := by
  constructor
  · exact GeneralHessenberg.slice_thick hP.thick 1 2 (by decide)
  · intro j
    fin_cases j
    · simpa [GeneralHessenberg.slice] using hP.gap_pos (1 : Fin 3)
    · simpa [GeneralHessenberg.slice] using hP.gap_pos (2 : Fin 3)
  · intro j
    fin_cases j
    · simpa [GeneralHessenberg.slice] using hP.gap_ne (1 : Fin 3)
    · simpa [GeneralHessenberg.slice] using hP.gap_ne (2 : Fin 3)
  · simpa [lastGap,GeneralHessenberg.slice,GeneralHessenberg.sliceEmbedding,
      OrderEmbedding.ofStrictMono,Fin.sum_univ_succ] using hP.bottom

theorem four_a_only_first_coefficient {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hb : P.r 1 ≠ q.val) (hc : P.r 2 ≠ q.val)
    (hv : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val) :
    firstCoefficient q P.toBetaDiagram.schur =
      (GeneralHessenberg.slice P 1 2 (by decide)).toBetaDiagram.schur := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hB : (P.r 1 : ℤ) ≠ q.val := by exact_mod_cast hb
  have hC : (P.r 2 : ℤ) ≠ q.val := by exact_mod_cast hc
  have hU : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  rw [← minimumPolynomial_coeff_one, four_marked_core hP,
    three_full_interval (suffix_three_component hP)]
  have haq : (P.r 0 : ℤ) = q.val := by exact_mod_cast ha
  simp only [if_pos haq,if_neg hB,if_neg hC,if_neg hU,if_neg hv,if_neg hX]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ]
  simp (failIfUnchanged := false) only [ha]
  have hS0 : (GeneralHessenberg.slice P 1 2 (by decide)).r 0 = P.r 1 := rfl
  have hS1 : (GeneralHessenberg.slice P 1 2 (by decide)).r 1 = P.r 2 := rfl
  have hS2 : (GeneralHessenberg.slice P 1 2 (by decide)).r 2 = P.r 3 := rfl
  have hG0 : (GeneralHessenberg.slice P 1 2 (by decide)).g 0 = P.g 1 := rfl
  have hG1 : (GeneralHessenberg.slice P 1 2 (by decide)).g 1 = P.g 2 := rfl
  simp only [threeInterval,hS0,hS1,hS2,hG0,hG1,suffixIndex]

theorem four_ab_square_first_augmentation {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 ≠ q.val) :
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight
      (firstCoefficient q P.toBetaDiagram.schur)) = -1 := by
  rw [four_ab_first_coefficient hP ha hb hc]
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  exact variable_times_B_square_augmentation (P.g 1) (P.g 2)
    ((q.val : ℤ) + P.r 2 - P.g 1) (P.r 3)
    (by exact_mod_cast hP.gap_pos 1) (by exact_mod_cast hP.gap_pos 2)
    (by omega) hd

theorem four_ab_scalar_zero {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 ≠ q.val) :
    residualAugmentation (restriction q P) = 0 ∧
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) = 0 := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hC : (P.r 2 : ℤ) ≠ q.val := by exact_mod_cast hc
  have hU : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by omega
  have hV : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val := by omega
  have hX : prefixIndex P ≠ q.val := by dsimp [prefixIndex]; omega
  have hzero : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 0 =
      residualAugmentation (restriction q P) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_zero, restriction]
  have hone : ((minimumPolynomial q P.toBetaDiagram.schur).map residualAugmentation).coeff 1 =
      residualAugmentation (firstCoefficient q P.toBetaDiagram.schur) := by
    simp only [Polynomial.coeff_map, minimumPolynomial_coeff_one]
  rw [← hzero, ← hone, four_scalar_marked hP]
  have haq : (P.r 0 : ℤ) = q.val := by exact_mod_cast ha
  have hbq : (P.r 1 : ℤ) = q.val := by exact_mod_cast hb
  simp only [scalarContactPolynomial,if_pos haq,if_pos hbq,if_neg hC,if_neg hU,
    if_neg hV,if_neg hX]
  norm_num [Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ]

/-- The AB restriction contracts to an actual, untouched three-row full function. -/
theorem four_ab_contract_full {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 ≠ q.val) :
    restriction q P = -complete (P.g 0) *
      (GeneralHessenberg.contract P 0).toBetaDiagram.schur := by
  have hC := four_endpoint_contract_component hP ha
  obtain ⟨hr0, hr1, hr2, hg0, hg1⟩ := four_endpoint_contract_coordinates P
  have hrg : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hr : P.g 0 < q.val := by omega
  have hfirstgt : (q.val : ℤ) < (GeneralHessenberg.contract P 0).r 0 := by omega
  have hmerge : ((GeneralHessenberg.contract P 0).r 0 : ℤ) +
      (GeneralHessenberg.contract P 0).r 1 - (GeneralHessenberg.contract P 0).g 0 ≠ q.val := by
    have h : (GeneralHessenberg.contract P 0).g 0 <
        (GeneralHessenberg.contract P 0).r 1 :=
      (GeneralHessenberg.contract P 0).g_lt_succ 0
    omega
  have hfree := three_no_contact_of_first_indices hC
    (by omega) (by rw [hr1]; exact hc) hmerge
  rw [four_endpoint_contract_restriction hP ha,
    restriction_eq_full_of_no_entry_contact hfree]

theorem four_ab_restriction_expansion {q : ℕ+} {P : Profile 3} (hP : QComponent q P)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 ≠ q.val) :
    restriction q P = -complete (P.g 0) *
      threeInterval complete (2 * (q.val : ℤ) - P.g 0) (P.r 2) (P.r 3)
        (P.g 1) (P.g 2) := by
  rw [four_ab_contract_full hP ha hb hc,
    three_full_interval (four_endpoint_contract_component hP ha)]
  obtain ⟨hr0, hr1, hr2, hg0, hg1⟩ := four_endpoint_contract_coordinates P
  rw [hr0, hr1, hr2, hg0, hg1, ha, hb]
  have he : (q.val : ℤ) + q.val - P.g 0 = 2 * q.val - P.g 0 := by ring
  rw [he]

private theorem three_tail_product_of_schur_eq (C D : Profile 2)
    (hfirst : C.r 0 = D.r 0)
    (he : C.toBetaDiagram.schur = D.toBetaDiagram.schur) :
    complete (C.r 1)*complete (C.r 2) = complete (D.r 1)*complete (D.r 2) := by
  have he' : C.schur = D.schur := by
    simpa only [Profile.toBetaDiagram_schur] using he
  have hr := (Profile.rows_eq_of_schur_eq he').2
  have hu : (Finset.univ : Finset (Fin 3)).val = {0,1,2} := by decide
  change (Finset.univ.val.map C.r) = (Finset.univ.val.map D.r) at hr
  simp only [hu,Multiset.map_cons,Multiset.map_zero,hfirst,
    Multiset.cons_inj_right] at hr
  have hp := congrArg
    (fun M : Multiset ℕ => (M.map (fun m => complete (m : ℤ))).prod) hr
  have hprod : complete (C.r 0)*(complete (C.r 1)*complete (C.r 2)) =
      complete (D.r 0)*(complete (D.r 1)*complete (D.r 2)) := by simpa using hp
  rw [hfirst] at hprod
  exact mul_left_cancel₀
    ((complete_ne_zero_iff (D.r 0)).mpr (by exact_mod_cast (D.r_pos 0).le)) hprod

/-- Paired AB first jets recover the two ordered tail rows from the unshifted
and shifted pair multisets, including a repeated contracted first row. -/
theorem four_first_jet_ab_pair {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 ≠ q.val)
    (hA : Q.r 0 = q.val) (hB : Q.r 1 = q.val) (hC : Q.r 2 ≠ q.val)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hdom := P.four_domain hP.thick.hessenberg
  have hDOM := Q.four_domain hQ.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  rcases hDOM with ⟨hR, hS, hT, hA', hB', hC', hD⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hBOTTOM : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have hjet := hone
  rw [four_ab_first_coefficient hP ha hb hc, four_ab_first_coefficient hQ hA hB hC] at hjet
  obtain ⟨hss, htt, hshift⟩ := variable_times_B_reading (P.g 1) (P.g 2)
    ((q.val : ℤ) + P.r 2 - P.g 1) (P.r 3) (Q.g 1) (Q.g 2)
    ((q.val : ℤ) + Q.r 2 - Q.g 1) (Q.r 3)
    (by exact_mod_cast hP.gap_pos 1) (by exact_mod_cast hQ.gap_pos 1)
    (by exact_mod_cast hP.gap_pos 2) (by omega) hd
    (by exact_mod_cast hQ.gap_pos 2) (by omega) hD hjet
  have hsNat : P.g 1 = Q.g 1 := by exact_mod_cast hss
  have htNat : P.g 2 = Q.g 2 := by exact_mod_cast htt
  have hsum := gap_sum_three_eq hP hQ (restriction_full_and_gap_eq hP hQ hzero).2
  have hrNat : P.g 0 = Q.g 0 := by omega
  let C := GeneralHessenberg.contract P 0
  let D := GeneralHessenberg.contract Q 0
  have hfull : C.toBetaDiagram.schur = D.toBetaDiagram.schur := by
    have he := hzero
    rw [four_ab_contract_full hP ha hb hc, four_ab_contract_full hQ hA hB hC, hrNat] at he
    exact mul_left_cancel₀
      (neg_ne_zero.mpr ((complete_ne_zero_iff (Q.g 0)).mpr (by positivity))) he
  obtain ⟨hrC0, hrC1, hrC2, hgC0, hgC1⟩ := four_endpoint_contract_coordinates P
  obtain ⟨hrD0, hrD1, hrD2, hgD0, hgD1⟩ := four_endpoint_contract_coordinates Q
  have hC0 : (C.r 0 : ℤ) = (P.r 0 : ℤ)+P.r 1-P.g 0 := hrC0
  have hD0 : (D.r 0 : ℤ) = (Q.r 0 : ℤ)+Q.r 1-Q.g 0 := hrD0
  have hfirst : C.r 0 = D.r 0 := by omega
  have hC1 : C.r 1 = P.r 2 := hrC1
  have hC2 : C.r 2 = P.r 3 := hrC2
  have hD1 : D.r 1 = Q.r 2 := hrD1
  have hD2 : D.r 2 = Q.r 3 := hrD2
  have hplain : complete (P.r 2)*complete (P.r 3) =
      complete (Q.r 2)*complete (Q.r 3) := by
    simpa only [hC1,hC2,hD1,hD2] using three_tail_product_of_schur_eq C D hfirst hfull
  have hpairs := complete_two_product_reading
    (show (0 : ℤ) < P.r 2 by exact_mod_cast P.r_pos 2)
    (show (0 : ℤ) < P.r 3 by exact_mod_cast P.r_pos 3)
    (show (0 : ℤ) < Q.r 2 by exact_mod_cast Q.r_pos 2)
    (show (0 : ℤ) < Q.r 3 by exact_mod_cast Q.r_pos 3) hplain
  have hcd : P.r 2 = Q.r 2 ∧ P.r 3 = Q.r 3 := by
    rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hshift with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  have hhighP := four_ab_higher_coefficients hP ha hb hc
  have hhighQ := four_ab_higher_coefficients hQ hA hB hC
  apply (four_schur_eq_iff_jet_and_higher hP hQ).mpr
  refine ⟨hzero, hone, ?_, ?_⟩
  · rw [hhighP.1, hhighQ.1, hcd.1, hcd.2, htNat]
  · rw [hhighP.2, hhighQ.2]

/-- The isolated U competitor of an AB jet is excluded by its extra private
proper-interval coefficient.  Divisibility supplies the candidate's first row. -/
theorem four_ab_u_first_jet_impossible {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 ≠ q.val)
    (hU : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = q.val) (hC : Q.r 2 ≠ q.val)
    (hV : (Q.r 1 : ℤ) + Q.r 2 - Q.g 1 ≠ q.val)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) : False := by
  have hdom := P.four_domain hP.thick.hessenberg
  have hDOM := Q.four_domain hQ.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  rcases hDOM with ⟨hR, hS, hT, hA', hB', hC', hD⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hBOTTOM : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have hjet := hone
  rw [four_ab_first_coefficient hP ha hb hc,
    four_u_only_first_coefficient hQ hU hC hV] at hjet
  obtain ⟨hss, htt, hshift⟩ := variable_times_B_reading (P.g 1) (P.g 2)
    ((q.val : ℤ) + P.r 2 - P.g 1) (P.r 3) (Q.g 0) (Q.g 2) (Q.r 2) (Q.r 3)
    (by exact_mod_cast hP.gap_pos 1) (by exact_mod_cast hQ.gap_pos 0)
    (by exact_mod_cast hP.gap_pos 2) (by omega) hd
    (by exact_mod_cast hQ.gap_pos 2) (by omega) hD hjet
  have hsNat : P.g 1 = Q.g 0 := by exact_mod_cast hss
  have htNat : P.g 2 = Q.g 2 := by exact_mod_cast htt
  have hsum := gap_sum_three_eq hP hQ (restriction_full_and_gap_eq hP hQ hzero).2
  have hrNat : P.g 0 = Q.g 1 := by omega
  have hCgt : (q.val : ℤ) + P.g 2 < Q.r 2 := by
    rcases hshift with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hDgt : (q.val : ℤ) + P.g 2 < Q.r 3 := by
    rcases hshift with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hrows : (Q.r 2 : ℤ) + Q.r 3 = (q.val : ℤ) + P.r 2 + P.r 3 - P.g 1 := by
    rcases hshift with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hAne : Q.r 0 ≠ q.val := by omega
  have hBne : Q.r 1 ≠ q.val := by omega
  let V : ℕ+ := ⟨Q.g 1, hQ.gap_pos 1⟩
  have hdiv : (MvPolynomial.X V : CompleteRing) ∣ restriction q Q := by
    rw [← complete_nat V]
    change complete (Q.g 1) ∣ restriction q Q
    rw [← hrNat, ← hzero, restriction_eq_monicContent_mul hP]
    have hcon : monicContent hP = complete (P.g 0) := by
      rw [four_content_first_row hP ha]
      simp [hc]
    rw [hcon]
    exact dvd_mul_right _ _
  have hconditions := (four_middle_gap_dvd_iff hQ hAne).mp hdiv
  have hAr : Q.r 0 = P.g 0 := by
    rcases hconditions with ⟨hb'', _⟩ | ⟨hc'', _⟩ | ⟨_, hrow⟩
    · exact (hBne hb'').elim
    · exact (hC hc'').elim
    · exact hrow.trans hrNat.symm
  have hsr : P.g 1 < P.g 0 := by
    have h : Q.g 0 < Q.r 0 := Q.g_lt_castSucc 0
    rw [← hsNat, hAr] at h
    exact h
  have hb0 : (Q.r 1 : ℤ) = (q.val : ℤ) + P.g 1 - P.g 0 := by omega
  have hq2r : 2 * (P.g 0 : ℤ) < q.val := by omega
  have hrawQ : restriction q Q = complete (P.g 0) *
      (complete ((q.val : ℤ) + P.g 1 - P.g 0) * complete (Q.r 2) * complete (Q.r 3) -
        complete (P.g 0) * complete ((q.val : ℤ) + P.g 1 - P.g 0 + Q.r 2 - P.g 0) *
          complete (Q.r 3) -
        complete (P.g 2) * complete ((q.val : ℤ) + P.g 1 - P.g 0) *
          complete ((Q.r 2 : ℤ) + Q.r 3 - P.g 2) +
        complete (P.g 1) * complete ((q.val : ℤ) + Q.r 2 - P.g 0) * complete (Q.r 3) +
        complete (P.g 0) * complete (P.g 2) *
          complete ((q.val : ℤ) + P.g 1 - P.g 0 + Q.r 2 + Q.r 3 - P.g 0 - P.g 2) -
        complete (P.g 1) * complete (P.g 2) *
          complete ((q.val : ℤ) + P.g 1 - P.g 0 + Q.r 2 + Q.r 3 - P.g 1 - P.g 2)) := by
    rw [restriction_four_expansion q Q hQ.thick]
    simp only [fourInterval, hU, bar_cut, mul_zero, zero_mul, sub_zero, add_zero]
    rw [bar_eq_complete_of_ne q (Q.r 0) (by exact_mod_cast hAne),
      bar_eq_complete_of_ne q (Q.r 1) (by exact_mod_cast hBne),
      bar_eq_complete_of_ne q (Q.r 2) (by exact_mod_cast hC),
      bar_eq_complete_of_ne q (Q.r 3) (by omega),
      bar_eq_complete_of_ne q (Q.g 0) (by exact_mod_cast hQ.gap_ne 0),
      bar_eq_complete_of_ne q (Q.g 1) (by exact_mod_cast hQ.gap_ne 1),
      bar_eq_complete_of_ne q (Q.g 2) (by exact_mod_cast hQ.gap_ne 2),
      bar_eq_complete_of_ne q _ hV,
      bar_eq_complete_of_ne q _ (by omega),
      bar_eq_complete_of_ne q _ (by omega),
      bar_eq_complete_of_ne q _ (by omega),
      bar_eq_complete_of_ne q _ (by omega)]
    rw [hAr, ← hsNat, ← hrNat, ← htNat, hb0]
    have hx : (P.g 0 : ℤ) + ((q.val : ℤ) + P.g 1 - P.g 0) + Q.r 2 -
        P.g 1 - P.g 0 = (q.val : ℤ) + Q.r 2 - P.g 0 := by ring
    have hf : (P.g 0 : ℤ) + ((q.val : ℤ) + P.g 1 - P.g 0) + Q.r 2 + Q.r 3 -
        P.g 1 - P.g 0 - P.g 2 =
      (q.val : ℤ) + P.g 1 - P.g 0 + Q.r 2 + Q.r 3 - P.g 1 - P.g 2 := by ring
    rw [hx, hf]
    ring
  have he := hzero
  rw [four_ab_restriction_expansion hP ha hb hc, hrawQ] at he
  have hfactor : -complete (P.g 0) *
      threeInterval complete (2 * (q.val : ℤ) - P.g 0) (P.r 2) (P.r 3) (P.g 1) (P.g 2) =
    complete (P.g 0) *
      (-threeInterval complete (2 * (q.val : ℤ) - P.g 0) (P.r 2) (P.r 3) (P.g 1) (P.g 2)) := by ring
  rw [hfactor] at he
  have he' := mul_left_cancel₀ ((complete_ne_zero_iff (P.g 0)).mpr (by positivity)) he
  exact ab_u_restriction_defect_ne q.val (P.g 0) (P.g 1) (P.g 2)
    (P.r 2) (P.r 3) (Q.r 2) (Q.r 3)
    (by exact_mod_cast hP.gap_pos 1) (by exact_mod_cast hsr)
    (by exact_mod_cast hP.gap_pos 2) hq2r hc'
    (by exact_mod_cast hbottom) hCgt hDgt hrows he'

/-- AB first-jet rigidity against every four-row mate.  The positive-initial
competitors are separated first, then the isolated U competitor is excluded
by the actual proper-interval marker. -/
theorem four_first_jet_ab {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 = q.val) (hb : P.r 1 = q.val) (hc : P.r 2 ≠ q.val)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hsc := four_ab_scalar_zero hP ha hb hc
  rw [hzero, hone] at hsc
  have hsign := congrArg
    (fun p : CompleteRing => residualAugmentation
      (Base.initialForm Base.squareWeight.generatorWeight p)) hone
  rw [four_ab_square_first_augmentation hP ha hb hc] at hsign
  have hdom := Q.four_domain hQ.thick.hessenberg
  rcases hdom with ⟨hR, hS, hT, hA', hB', hC', hD⟩
  have hBOTTOM : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  rcases four_scalar_zero_contact_cases hQ hsc with hnone | ⟨hA, hB, hC, hV⟩ |
    ⟨hB, hA, hC⟩ | ⟨hC, hA, hB, hU⟩ | ⟨hU, hC, hV⟩ | ⟨hA, hB, hC⟩
  · rw [firstCoefficient_zero_of_no_contact hnone, Base.initialForm_zero, map_zero] at hsign
    norm_num at hsign
  · rw [four_a_only_first_coefficient hQ hA hB hC hV,
      profile_square_initial_augmentation] at hsign
    norm_num at hsign
  · rw [four_b_only_first_coefficient hQ hB hA hC,
      negative_variable_times_B_square_augmentation (Q.r 0) (Q.g 2) (Q.r 2) (Q.r 3)
        (by exact_mod_cast Q.r_pos 0) (by exact_mod_cast hQ.gap_pos 2)
        (by omega) hD] at hsign
    norm_num at hsign
  · rw [four_c_only_first_coefficient hQ hC hA hB hU,
      negative_variable_times_B_square_augmentation (Q.r 3) (Q.g 0) (Q.r 0) (Q.r 1)
        (by exact_mod_cast Q.r_pos 3) (by exact_mod_cast hQ.gap_pos 0)
        hA' (by omega)] at hsign
    norm_num at hsign
  · exact (four_ab_u_first_jet_impossible hP hQ ha hb hc hU hC hV hzero hone).elim
  · exact four_first_jet_ab_pair hP hQ ha hb hc hA hB hC hzero hone

/-- Outside the six double-contact patterns, both higher coefficients vanish.
Every condition is a numerical contact condition in the actual profile. -/
theorem four_higher_zero_of_no_double_contacts {q : ℕ+} {P : Profile 3}
    (hab : ¬ (P.r 0 = q.val ∧ P.r 1 = q.val))
    (hac : ¬ (P.r 0 = q.val ∧ P.r 2 = q.val))
    (hbc : ¬ (P.r 1 = q.val ∧ P.r 2 = q.val))
    (huc : ¬ ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 2 = q.val))
    (hav : ¬ (P.r 0 = q.val ∧ (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val)) :
    fourSecondCoefficient q P = 0 ∧ fourThirdCoefficient q P = 0 := by
  have habc : ¬ (P.r 0 = q.val ∧ P.r 1 = q.val ∧ P.r 2 = q.val) :=
    fun h => hab ⟨h.1, h.2.1⟩
  simp [fourSecondCoefficient, fourThirdCoefficient, hab, hac, hbc, huc, hav, habc]

/-- First-jet recovery on every four-row contact stratum.  The proof uses the
actual restriction and first coefficient, not an assumed residual classification. -/
theorem staircase_first_jet_four {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  by_cases hab : P.r 0 = q.val ∧ P.r 1 = q.val
  · by_cases hc : P.r 2 = q.val
    · exact four_first_jet_abc hP hQ hab.1 hab.2 hc hzero hone
    · exact four_first_jet_ab hP hQ hab.1 hab.2 hc hzero hone
  by_cases hac : P.r 0 = q.val ∧ P.r 2 = q.val
  · exact four_first_jet_ac hP hQ hac.1 hac.2
      (fun hb => hab ⟨hac.1, hb⟩) hzero hone
  by_cases hbc : P.r 1 = q.val ∧ P.r 2 = q.val
  · exact four_first_jet_bc hP hQ (fun ha => hab ⟨ha, hbc.1⟩)
      hbc.1 hbc.2 hzero hone
  by_cases huc : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 2 = q.val
  · exact four_first_jet_uc hP hQ huc.1 huc.2 hzero hone
  by_cases hav : P.r 0 = q.val ∧ (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val
  · exact four_first_jet_av hP hQ hav.1 hav.2 hzero hone
  by_cases hAB : Q.r 0 = q.val ∧ Q.r 1 = q.val
  · by_cases hC : Q.r 2 = q.val
    · exact (four_first_jet_abc hQ hP hAB.1 hAB.2 hC hzero.symm hone.symm).symm
    · exact (four_first_jet_ab hQ hP hAB.1 hAB.2 hC hzero.symm hone.symm).symm
  by_cases hAC : Q.r 0 = q.val ∧ Q.r 2 = q.val
  · exact (four_first_jet_ac hQ hP hAC.1 hAC.2
      (fun hB => hAB ⟨hAC.1, hB⟩) hzero.symm hone.symm).symm
  by_cases hBC : Q.r 1 = q.val ∧ Q.r 2 = q.val
  · exact (four_first_jet_bc hQ hP (fun hA => hAB ⟨hA, hBC.1⟩)
      hBC.1 hBC.2 hzero.symm hone.symm).symm
  by_cases hUC : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = q.val ∧ Q.r 2 = q.val
  · exact (four_first_jet_uc hQ hP hUC.1 hUC.2 hzero.symm hone.symm).symm
  by_cases hAV : Q.r 0 = q.val ∧ (Q.r 1 : ℤ) + Q.r 2 - Q.g 1 = q.val
  · exact (four_first_jet_av hQ hP hAV.1 hAV.2 hzero.symm hone.symm).symm
  have hhighP := four_higher_zero_of_no_double_contacts hab hac hbc huc hav
  have hhighQ := four_higher_zero_of_no_double_contacts hAB hAC hBC hUC hAV
  apply (four_schur_eq_iff_jet_and_higher hP hQ).mpr
  refine ⟨hzero, hone, ?_, ?_⟩
  · rw [hhighP.1, hhighQ.1]
  · rw [hhighP.2, hhighQ.2]

/-- The manuscript's full first-jet theorem, for actual q-components with at
most four rows.  Equal restrictions recover the mate's row count as well. -/
theorem staircase_first_jet {n m : ℕ} {q : ℕ+}
    {P : Profile n} {Q : Profile m} (hP : QComponent q P) (hQ : QComponent q Q)
    (hn : n ≤ 3) (hzero : restriction q P = restriction q Q)
    (hone : firstCoefficient q P.toBetaDiagram.schur =
      firstCoefficient q Q.toBetaDiagram.schur) :
    P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
  have hnm := row_count_eq_of_restriction_eq hP hQ hzero
  subst m
  interval_cases n
  · exact staircase_first_jet_singleton hP hQ hzero
  · exact staircase_first_jet_two hP hQ hzero hone
  · exact staircase_first_jet_three hP hQ hzero hone
  · exact staircase_first_jet_four hP hQ hzero hone

end SkewJacobiNegative.Staircase
